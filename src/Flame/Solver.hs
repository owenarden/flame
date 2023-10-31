{-|

Solver for Flow-limited authorization acts-for constraints, by Owen Arden.

Based heavily on https://github.com/clash-lang/ghc-typelits-natnormalise
by Christiaan Baaij <christiaan.baaij@gmail.com>.
License: BSD2

A type checker plugin for GHC that can solve FLAM acts-for contraints
on types of kind 'Flame.Principals.KPrin'.

To use the plugin, add

@
{\-\# OPTIONS_GHC -fplugin Flame.Solver \#-\}
@

To the header of your file.
-}

{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module Flame.Solver
  ( plugin )
where

-- external
import Control.Arrow              (second)
import Control.Monad              (replicateM, msum)
import Data.List                  (partition)
import qualified Data.Set as S    (union, empty, singleton, notMember, toList)
import Data.Maybe                 (mapMaybe, maybeToList, catMaybes)
import Data.Map.Strict as M       (Map, foldlWithKey, empty, fromList, unionWith, findWithDefault, union, keys, toList, mapWithKey, keysSet, elems, lookup, singleton)
-- GHC API
import GHC (lookupModule, lookupName)
import GHC.Plugins hiding (TcPlugin)
--    ( Plugin(tcPlugin),
--      heqDataCon,
--      heqTyCon,
--      mkForAllCos,
--      mkHoleCo,
--      mkInstCo,
--      mkNomReflCo,
--      mkPrimEqPred,
--      mkUnivCo,
--      dataConWrapId,
--      promoteDataCon,
--      mkTyVarTy,
--      mkTyConApp,
--      typeKind,
--      fsLit,
--      defaultPlugin,
--      pprTrace,
--      mkDataOcc,
--      mkTcOcc,
--      uniqSets
--      unionUniqSets,
--      mkModuleName,
--      Role(Representational),
--      CoercionHole,
--      PredType,
--      Type,
--      TyCon(tyConUnique),
--      -- TcPlugin,
--      TyVar,
--      Outputable(ppr) ) 
import GHC.Tc.Types
    ( TcPluginM,
      unsafeTcPluginTcM,
      TcPlugin(TcPlugin, tcPluginStop, tcPluginInit, tcPluginSolve),
      TcPluginResult(TcPluginOk) )
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Core.Predicate
import GHC.Core.TyCo.Rep

-- import FastString (fsLit)

-- internal
import Flame.Solver.Data
import Flame.Solver.Unify
import Flame.Solver.Norm
import Flame.Solver.ActsFor
import GHC (NamedThing(..))
import GHC.Tc.Plugin
import GHC.Tc.Solver.Monad
import GHC.Tc.Utils.TcType

-- #if __GLASGOW_HASKELL__ >= 82
-- uniqSetToList = nonDetEltsUniqSet
-- #endif


plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const $ Just flamePlugin }

flamePlugin :: TcPlugin
flamePlugin = -- tracePlugin "flame"
  TcPlugin { tcPluginInit  = lookupFlameRec
           , tcPluginSolve = decideActsFor
           , tcPluginStop  = \_ -> (return ())
           }

lookupFlameRec :: TcPluginM FlameRec
lookupFlameRec = do
    md         <- lookupModule flameModule Nothing --flamePackage
    kprinTc    <- tcLookupTyCon (getName $ mkTcOcc "KPrin")
    actsforTc  <- tcLookupTyCon (getName $ mkTcOcc "≽")
    ktopData   <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KTop")  
    kbotData   <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KBot")  
    knameData  <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KName")
    kconjData  <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KConj")
    kdisjData  <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KDisj")
    kconfData  <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KConf")
    kintegData <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KInteg")
    kvoiceData <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KVoice")
    keyeData   <- promoteDataCon <$> tcLookupDataCon (getName $ mkDataOcc "KEye")
    (level,_)    <- unsafeTcPluginTcM $ runTcS getTcLevel
    return FlameRec{
       kprin      = kprinTc
    ,  actsfor    = actsforTc
    ,  ktop       = ktopData
    ,  kbot       = kbotData
    ,  kname      = knameData
    ,  kconj      = kconjData
    ,  kdisj      = kdisjData
    ,  kconf      = kconfData
    ,  kinteg     = kintegData
    ,  kvoice     = kvoiceData
    ,  keye       = keyeData
    ,  confBounds   = M.empty
    ,  integBounds  = M.empty
    ,  confClosure  = []
    ,  integClosure = []
    ,  tclevel      = level
    }
  where
    flameModule  = mkModuleName "Flame.Principals"
    flamePackage = fsLit "flame"

decideActsFor :: FlameRec -> [Ct] -> [Ct] -> [Ct]
               -> TcPluginM TcPluginResult
decideActsFor _ _givens _deriveds []      = return (TcPluginOk [] [])
decideActsFor _flrec givens  _deriveds wanteds = do
    (level, _) <- unsafeTcPluginTcM $ runTcS getTcLevel
    let flrec = _flrec{tclevel = level}
    -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
    let wanteds' = filter (isWanted . ctEvidence) wanteds
    let unit_wanteds = concat $ map (toActsFor flrec) wanteds'
    -- XXX: natnormalise zonkCt's these givens, but that appears to remove the ones I care about.
    let unit_givens = concat $ map (toActsFor flrec) givens
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        sr <- solvePrins flrec unit_givens unit_wanteds
        tcPluginTrace "flame-normalized" (ppr sr)
        case sr of
          Simplified evs -> do
            let solved = filter (isWanted . ctEvidence . (\(_,x) -> x)) (fst evs)
                newWanteds = snd evs
            return (TcPluginOk solved newWanteds)
          Impossible eq@(ct, (p, q)) -> do
             --return (TcPluginContradiction [fromActsFor eq])
             pprTrace ("Cannot prove "
                      ++ (outputKPrin flrec (reifyNorm flrec p))
                      ++  " ≽ "
                      ++ (outputKPrin flrec (reifyNorm flrec q))
                      ++ " with context ["
                      ++ foldl (\ctx eq@(ct, (p, q)) ->
                                  ctx ++ "("
                                  ++ (outputKPrin flrec (reifyNorm flrec p))
                                  ++  " ≽ "
                                  ++ (outputKPrin flrec (reifyNorm flrec q))
                                  ++ ")"
                               ) "" unit_givens
                       ++ "]"
                      ) (ppr "") $
               return (TcPluginOk [] [])

solvePrins :: FlameRec
             -> [ActsForCt]
             -> [ActsForCt]
             -> TcPluginM SimplifyResult
solvePrins flrec givens afcts =
      -- vars are only substituted in actsfor given a set of bounds.
      -- BUT: what about structural superiors?
    let (conf_givens_flat, integ_givens_flat) = flattenDelegations (map snd givens)
        conf_closure =  computeDelClosure conf_givens_flat
        integ_closure = computeDelClosure integ_givens_flat
    in -- pprTrace "confclosure" (ppr conf_closure) $ pprTrace "integclosure" (ppr integ_closure) $
    do 
     tcPluginTrace "solvePrins" (ppr afcts)
     solve flrec{confClosure = conf_closure, integClosure = integ_closure,
                 confBounds = initVarMap, integBounds = initVarMap}
           indexedAFs
  where
    allVars = concat [uniqSetToList $ fvNorm p `unionUniqSets` fvNorm q | (ct, (p, q)) <- afcts]

    initVarMap :: Map TyVar CoreJNorm
    initVarMap = fromList $ map (\v -> (v, J [M [B]])) $ [v | v <- allVars, isTouchableMetaTyVar (tclevel flrec) v]

    indexedAFCTs = zip [0..length afcts] afcts
    indexedAFs = map (\(i, (ct, af)) -> (i, af)) $ indexedAFCTs
    lookupCT i = fst $ afcts !! i

    confAFToVarDeps = fromList $ map (\(i, (ct, af@(N p _, N q _))) -> ((i, af), touchableFVs q)) $ indexedAFCTs 
    confVarToAFDeps = foldl (\deps (iaf, vars) -> 
                              unionWith (S.union) (fromList [(v, S.singleton iaf) | v <- vars]) deps)
                            M.empty $ toList confAFToVarDeps

    integAFToVarDeps = fromList $ map (\(i, (ct, af@(N _ p, N _ q))) -> ((i, af), touchableFVs q)) $ indexedAFCTs 
    integVarToAFDeps = foldl (\deps (iaf, vars) -> 
                              unionWith (S.union) (fromList [(v, S.singleton iaf) | v <- vars]) deps)
                             M.empty $ toList integAFToVarDeps

    touchableFVs p = [ v | v <- uniqSetToList $ fvJNorm p, isTouchableMetaTyVar (tclevel flrec) v ]

    solve :: FlameRec
            -> [(Int, (CoreNorm, CoreNorm))]
            -> TcPluginM SimplifyResult
    solve flrec iafs = do
      -- solve on uninstantiated vars. return updated bounds
      let sr = ( search flrec True [] iafs []
               , search flrec False [] iafs [])
      tcPluginTrace "search result" (ppr sr)
      case sr of
        (Lose af, _) -> -- pprTrace "impossible: " (ppr af) $
          return (Impossible af)
        (_, Lose af) -> -- pprTrace "impossible: " (ppr af) $
          return (Impossible af)
        (cnf, intg) -> do
          let cnf' = resultBounds cnf
              intg' = resultBounds intg
              new_flrec = updateBounds (updateBounds flrec True cnf') False intg'
              solved_cts = map (lookupCT . fst) iafs
          preds <- boundsToPredTypes new_flrec 
          (ev, wanted) <- evMagic new_flrec solved_cts preds
          {- pprTrace "solved bounds: " (ppr cnf' <+> ppr intg') $-}
          return $ Simplified (ev, wanted)

    wakeup isConf solved chg = let varToDeps = if isConf then confVarToAFDeps else integVarToAFDeps
                                   eqns = foldl (\deps v ->
                                                   (findWithDefault S.empty v varToDeps) `S.union` deps)
                                                S.empty
                                                chg
                               in partition (\eq -> (S.notMember eq eqns)) solved

    search :: FlameRec
           -> Bool
           -> [(Int, (CoreNorm, CoreNorm))]
           -> [(Int, (CoreNorm, CoreNorm))]
           -> [(TyVar, CoreJNorm)]
           -> SolverResult
    search flrec isConf solved [] changes = case changes of 
                                              [] -> Win
                                              _ -> ChangeBounds changes
    search flrec isConf solved (af@(i,(u@(N cp ip), v@(N cq iq))):iafs) changes =
      -- solve on uninstantiated vars. return updated bounds
      let sr = refineBoundsIfNeeded flrec isConf solved (af:iafs)
      in case sr of
         Win  -> search flrec isConf (af:solved) iafs changes
         Lose af' -> Lose af'
         ChangeBounds bnds -> 
           -- update bounds and re-solve: this ensures all members of solved are only added via 'Win'
           let new_flrec = updateBounds flrec isConf bnds
               vchgd = map fst bnds
               (solved', to_awake) = wakeup isConf solved vchgd
           in search new_flrec isConf solved' (af:(to_awake ++ iafs)) (bnds ++ changes)

    refineBoundsIfNeeded flrec isConf solved (af@(i,(u@(N cp ip), v@(N cq iq))):iafs) =
      let p      = if isConf then cp else ip
          q      = if isConf then cq else iq
          bounds = getBounds flrec isConf
          p' = substJNorm (tclevel flrec) bounds isConf p
          q' = substJNorm (tclevel flrec) bounds isConf q
      -- XXX: l bounded with a \/ b doesn't act for a \/ b
      in case actsForJ flrec isConf p' q' of
        Just pf -> Win
        Nothing -> 
          case touchableFVs p of
            [] -> Lose (lookupCT (fst af), snd af)
            [var] -> case joinWith q (findWithDefault jbot var bounds) of
                       Just bnd -> ChangeBounds [(var, bnd)]
                       Nothing -> Lose (lookupCT (fst af), snd af)
            vars -> let tryvar vs = case vs of
                          [] -> Lose (lookupCT (fst af), snd af)
                          (v:vs') -> case joinWith q (findWithDefault jbot v bounds) of
                                      Just bnd ->
                                        -- so far so good. recurse with this bound set.
                                        let new_flrec = updateBounds flrec isConf [(v, bnd)]
                                        in case search new_flrec isConf solved (af:iafs) [] of
                                             -- couldn't solve, try next vars
                                             Lose af -> tryvar vs' 
                                             -- solved with this change, return it
                                             Win -> ChangeBounds [(v, bnd)] 
                                             -- solved with this and other changes, return them
                                             ChangeBounds changes -> ChangeBounds ((v, bnd):changes)
                                      Nothing -> tryvar vs'
                    in tryvar vars
    joinWith q bnd = let new_bnd = mergeJNormJoin bnd q
                     in if new_bnd == bnd then
                           Nothing
                         else
                           Just new_bnd


-- Extract the actsfor constraints
toActsFor :: FlameRec -> Ct -> [ActsForCt]
toActsFor flrec ct = --pprTrace "toActsFor Ct:" (ppr ct) $
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq af@(TyConApp tc [p,q]) fsk
      | tc == (actsfor flrec) -> maybeToList $ toAFCt (p,q)

    EqPred NomEq p q
      | isKPrinKind (typeKind p) && isKPrinKind (typeKind q) 
        -> catMaybes [toAFCt (p, q), toAFCt (q, p)]

    IrredPred af -> maybeToList $ do pair <- maybeActsFor af
                                     toAFCt pair

    ClassPred cls afs | isCTupleClass cls ->
      let pairs = mapMaybe maybeActsFor afs
      in mapMaybe toAFCt pairs

    EqPred NomEq p q -> []

    _ -> []
 where
   isKPrinKind (TyConApp tc _) = tyConUnique tc == tyConUnique (kprin flrec)
   isKPrinKind _ = False
   maybeActsFor af = case af of
                       TyConApp tc [p,q]
                         | tc == (actsfor flrec) -> Just (p, q)
                       af -> Nothing
   toAFCt (p, q) = do sup <- normPrin flrec p
                      inf <- normPrin flrec q
                      return (ct, (sup, inf))
                         
boundsToPredTypes :: FlameRec -> TcPluginM [PredType]
boundsToPredTypes flrec = do
   ps <- mapM (\v -> do
                    c <- newFlexiTyVar $ TyConApp (kprin flrec) []
                    i <- newFlexiTyVar $ TyConApp (kprin flrec) []
                    let basePred = mkPrimEqPred (mkTyVarTy v)
                                    (mkTyConApp (kconj flrec)
                                     [(mkTyConApp (kconf flrec) [reifyBase flrec (V c)]), 
                                      (mkTyConApp (kinteg flrec) [reifyBase flrec (V i)])])
                        confPred = mkPrimEqPred (mkTyVarTy c)
                                                (reifyJNorm flrec $
                                                 findWithDefault jbot v (confBounds flrec))
                        integPred = mkPrimEqPred (mkTyVarTy i)
                                                (reifyJNorm flrec $ 
                                                 findWithDefault jbot v (integBounds flrec))
                    return $ [basePred, confPred, integPred])
                  (S.toList allVars)
   return $ concat ps
  where
    allVars = (keysSet $ confBounds flrec) `S.union` (keysSet $ integBounds flrec) 

evMagic :: FlameRec -> [Ct] -> [PredType] -> TcPluginM ([(EvTerm, Ct)], [Ct])
evMagic flrec cts preds = 
  let afscts = mapMaybe (\ct -> case classifyPredType $ ctEvPred $ ctEvidence ct of
                EqPred NomEq af fsk -> Just (af, ct)
                IrredPred af -> Just (af, ct)
                ClassPred cls (af:afs)
                  | isCTupleClass cls -> Just (af,ct) --XXX: HACK: only using first
                _ -> Nothing) cts
  in doMagic afscts
 where
   doMagic :: [(PredType, Ct)] -> TcPluginM ([(EvTerm, Ct)], [Ct])
   doMagic [] = return ([], [])
   doMagic afcts@((af,ct):_) = do
       --holes <- replicateM (length preds) newCoercionHole
       holes <- mapM newCoercionHole preds
       --XXX ugh. what ctLoc to use here?
       let newWanted = zipWith (unifyItemToCt (ctLoc ct)) preds holes
           holeEvs   = map mkHoleCo holes
           kprinReflCo = mkNomReflCo $ TyConApp (kprin flrec) []
           kprinCoBndr = (,kprinReflCo) <$> (newFlexiTyVar $  TyConApp (kprin flrec) [])
       evs <- mapM (\(af', ct') -> case af' of
                TyConApp tc [p,q] | tc == (actsfor flrec) -> do
                  let ctEv = mkUnivCo (PluginProv "flame") Representational (mkHEqPred p q) af'
                  forallEv <- mkForAllCos <$> (replicateM (length preds) kprinCoBndr) <*> pure ctEv
                  let finalEv = foldl mkInstCo forallEv holeEvs
                  return $ Just (evDFunApp (dataConWrapId heqDataCon)
                                [typeKind p, typeKind q, p, q]
                                [evByFiat "flame" p q] `EvCast` finalEv, ct')
                _ -> return Nothing) afcts
       
       return (catMaybes evs, newWanted)

unifyItemToCt :: CtLoc
              -> PredType
              -> CoercionHole
              -> Ct
#if __GLASGOW_HASKELL__ < 82
unifyItemToCt loc pred_type hole = mkNonCanonical (CtWanted pred_type (HoleDest hole) loc)
#else
unifyItemToCt loc pred_type hole = mkNonCanonical (CtWanted pred_type (HoleDest hole) WDeriv loc)
#endif

mkHEqPred :: Type -> Type -> Type
mkHEqPred t1 t2 = TyConApp heqTyCon [typeKind t1, typeKind t2, t1, t2]

-- | Used when we generate new constraints.
-- The boolean indicates if we are generateing a given or
-- a derived constraint.
mkNewEqFact :: CtLoc -> (Type,Type) -> TcPluginM CtEvidence
mkNewEqFact newLoc (t1,t2) = newGiven newLoc newPred (evByFiat "flame" t1 t2)
  where
  newPred = mkPrimEqPred t1 t2

mkNewAFFact :: FlameRec -> CtLoc -> (Type,Type) -> TcPluginM CtEvidence
mkNewAFFact flrec newLoc (t1,t2) = newGiven newLoc newPred (evByFiat "flame" t1 t2)
  where
  newPred = mkTyConApp (actsfor flrec) [t1, t2]

