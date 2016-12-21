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
import Data.Map.Strict as M       (Map, foldlWithKey, empty, fromList, unionWith, findWithDefault, union, keys, toList, mapWithKey, keysSet, elems, lookup)
-- GHC API
import UniqSet             (uniqSetToList, unionUniqSets)
import TcType              (isSkolemTyVar)

import Outputable (Outputable (..), (<+>), ($$), text, ppr, pprTrace)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (..))
import TcPluginM  (TcPluginM, tcPluginTrace, zonkCt, tcLookupTyCon, tcLookupDataCon,
                   tcPluginIO)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred, IrredPred, ClassPred), PredType,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy, mkPrimEqPred, isCTupleClass, typeKind, mkTyConApp, TyVar)
import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar)
import TcRnTypes  (CtEvidence (..), CtLoc, TcEvDest (..), ctLoc)
import TyCoRep    (UnivCoProvenance (..), Type (..))
import FastString (fsLit)
import GHC.TcPluginM.Extra (lookupModule, lookupName, newGiven, tracePlugin, evByFiat)
import OccName    (mkTcOcc, mkDataOcc, mkClsOcc)
import Module     (mkModuleName)
import DataCon (promoteDataCon, dataConWrapId)
import TysWiredIn  ( heqDataCon, heqTyCon )

-- internal
import Flame.Solver.Data
import Flame.Solver.Unify
import Flame.Solver.Norm


plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const $ Just flamePlugin }

flamePlugin :: TcPlugin
flamePlugin = tracePlugin "flame"
  TcPlugin { tcPluginInit  = lookupFlameRec
           , tcPluginSolve = decideActsFor
           , tcPluginStop  = \_ -> (return ())
           }

lookupFlameRec :: TcPluginM FlameRec
lookupFlameRec = do
    md         <- lookupModule flameModule flamePackage
    kprinTcNm    <- lookupName md (mkTcOcc "KPrin")
    actsforTcNm  <- lookupName md (mkTcOcc "≽")
    ktopDataNm   <- lookupName md (mkDataOcc "KTop")
    kbotDataNm   <- lookupName md (mkDataOcc "KBot")
    knameDataNm  <- lookupName md (mkDataOcc "KName")
    kconjDataNm  <- lookupName md (mkDataOcc "KConj")
    kdisjDataNm  <- lookupName md (mkDataOcc "KDisj")
    kconfDataNm  <- lookupName md (mkDataOcc "KConf")
    kintegDataNm <- lookupName md (mkDataOcc "KInteg")
    kvoiceDataNm <- lookupName md (mkDataOcc "KVoice")
    keyeDataNm   <- lookupName md (mkDataOcc "KEye")
    kprinTc    <- tcLookupTyCon kprinTcNm
    actsforTc  <- tcLookupTyCon actsforTcNm
    ktopData   <- promoteDataCon <$> tcLookupDataCon ktopDataNm
    kbotData   <- promoteDataCon <$> tcLookupDataCon kbotDataNm
    knameData  <- promoteDataCon <$> tcLookupDataCon knameDataNm
    kconjData  <- promoteDataCon <$> tcLookupDataCon kconjDataNm
    kdisjData  <- promoteDataCon <$> tcLookupDataCon kdisjDataNm
    kconfData  <- promoteDataCon <$> tcLookupDataCon kconfDataNm
    kintegData <- promoteDataCon <$> tcLookupDataCon kintegDataNm
    kvoiceData <- promoteDataCon <$> tcLookupDataCon kvoiceDataNm
    keyeData   <- promoteDataCon <$> tcLookupDataCon keyeDataNm
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
    ,  confBounds   = empty
    ,  integBounds  = empty
    ,  confClosure  = []
    ,  integClosure = []
    }
  where
    flameModule  = mkModuleName "Flame.Principals"
    flamePackage = fsLit "flame"

decideActsFor :: FlameRec -> [Ct] -> [Ct] -> [Ct]
               -> TcPluginM TcPluginResult
decideActsFor _ _givens _deriveds []      = return (TcPluginOk [] [])
decideActsFor flrec givens  _deriveds wanteds = do
    -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
    let wanteds' = filter (isWanted . ctEvidence) wanteds
    let unit_wanteds = concat $ map (toActsFor flrec) wanteds'
    -- XXX: natnormalise zonkCt's these givens, but that appears to remove the ones I care about.
    -- TODO: should also extract NomEq predicates on principal vars to peg their bounds: just subst them everywhere, I guess?
    let unit_givens = concat $ map (toActsFor flrec) givens
    --pprTrace "wanted: " (ppr unit_wanteds) $
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        sr <- simplifyPrins flrec unit_givens unit_wanteds
        --pprTrace "simplfied: " (ppr sr) $
        tcPluginTrace "flame-normalized" (ppr sr)
        case sr of
          Simplified evs -> do
            let solved = filter (isWanted . ctEvidence . (\(_,x) -> x)) (fst evs)
                newWanteds = snd evs
            return (TcPluginOk solved $ pprTrace "new wanteds" (ppr newWanteds) newWanteds)
          Impossible eq ->
            {- pprTrace "failed: " (ppr eq) $ -}
            -- return (TcPluginContradiction [fromActsFor eq])
            return (TcPluginOk [] [])

type ActsForCt = (Ct, (CoreNorm, CoreNorm))

fromActsFor :: ActsForCt -> Ct
fromActsFor (ct, _)    = ct

data SimplifyResult
  = Simplified ([(EvTerm,Ct)],[Ct])
  | Impossible ActsForCt

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

-- TODO: need to change from evs to "sovled" cts, then generate evidence all at once.
simplifyPrins :: FlameRec
             -> [ActsForCt]
             -> [ActsForCt]
             -> TcPluginM SimplifyResult
simplifyPrins flrec givens afcts =
      -- vars are only substituted in actsfor given a set of bounds.
      -- BUT: what about structural superiors?
    let (conf_givens_flat, integ_givens_flat) = flattenDelegations (map snd givens)
        conf_closure =  computeDelClosure conf_givens_flat
        integ_closure = computeDelClosure integ_givens_flat
        flrec' = flrec{confClosure = conf_closure, integClosure = integ_closure,
                       confBounds = bottomVarMap, integBounds = bottomVarMap}
    in pprTrace "simplify: " (ppr afcts <+> ppr bottomVarMap) $ tcPluginTrace "simplifyPrins" (ppr afcts) >> simples flrec' [] indexedAFs
  where
    allVars = concat [uniqSetToList $ fvNorm p `unionUniqSets` fvNorm q | (ct, (p, q)) <- afcts]
    bottomVarMap :: Map TyVar CoreJNorm
    bottomVarMap = fromList $ map (\v -> (v, J [M [B]])) $ [v | v <- allVars, not (isSkolemTyVar v)]
    indexedAFCTs = zip [0..length afcts] afcts
    indexedAFs = map (\(i, (ct, af)) -> (i, af)) $ indexedAFCTs
    lookupCT i = fst $ afcts !! i
    confAFToVarDeps = fromList $ map (\(i, (ct, af@(N p _, N q _))) -> ((i, af), uniqSetToList $ fvJNorm q)) $ indexedAFCTs 
    confVarToAFDeps = foldl (\deps (iaf, vars) -> 
                              unionWith (S.union) (fromList [(v, S.singleton iaf) | v <- vars]) deps)
                            empty $ toList confAFToVarDeps

    integAFToVarDeps = fromList $ map (\(i, (ct, af@(N _ p, N _ q))) -> ((i, af), uniqSetToList $ fvJNorm q)) $ indexedAFCTs 
    integVarToAFDeps = foldl (\deps (iaf, vars) -> 
                              unionWith (S.union) (fromList [(v, S.singleton iaf) | v <- vars]) deps)
                             empty $ toList integAFToVarDeps

    simples :: FlameRec
            -> [(Int, (CoreNorm, CoreNorm))]
            -> [(Int, (CoreNorm, CoreNorm))]
            -> TcPluginM SimplifyResult
    simples flrec solved [] = do
      let solved_cts = map (lookupCT . fst) solved
      preds <- boundsToPredTypes flrec 
      (ev, wanted) <- evMagic flrec solved_cts preds
      return $ Simplified (ev, wanted)
    simples flrec solved (af@(i,(u,v)):iafs) = do
      -- solve on uninstantiated vars. return updated bounds
      ur <- solvePrins flrec u v
      pprTrace "solvePrins" (ppr ur) $ tcPluginTrace "solvePrins result" (ppr ur)
      case ur of
        (Win, Win) -> simples flrec (af:solved) iafs
        (Lose, _) -> pprTrace "conf: could not satisfy" ((ppr af) <+> (ppr (confBounds flrec))) $ return (Impossible (lookupCT (fst af), snd af))
        (_, Lose) -> pprTrace "integ: could not satisfy" ((ppr af) <+> (ppr (integBounds flrec))) $ return (Impossible (lookupCT (fst af), snd af))
        (cnf, intg) -> -- update bounds
          -- update bounds and re-solve: this ensures all members of solved are only added via 'Win'
          let (confChanged, new_confBounds) = new_bounds flrec True cnf
              (integChanged, new_integBounds) = new_bounds flrec False intg
              (solved', to_awake) = wakeup solved confChanged integChanged
          in pprTrace "changed / new bounds " (ppr confChanged <+> ppr integChanged <+> ppr new_confBounds <+> ppr new_integBounds) $
            simples flrec{confBounds = new_confBounds, integBounds = new_integBounds}
                     solved' (af:(to_awake ++ iafs))
    wakeup solved confchg integchg = let confDeps = foldl (\deps v ->
                                                             (findWithDefault S.empty v confVarToAFDeps) `S.union` deps)
                                                          S.empty
                                                          confchg
                                         integDeps = foldl (\deps v ->
                                                             (findWithDefault S.empty v integVarToAFDeps) `S.union` deps)
                                                           S.empty
                                                           integchg
                                  in partition (\eq -> (S.notMember eq confDeps) && (S.notMember eq integDeps)) solved
    new_bounds flrec isConf result =
      case result of
        ChangeBounds bnds -> let changed = fromList bnds
                             in ( pprTrace "keys" (ppr bnds <+> ppr changed) $ keys changed
                                , union changed
                                        (if isConf then (confBounds flrec) else (integBounds flrec)))
        Win -> if isConf then ([], (confBounds flrec)) else ([], (integBounds flrec))
        Lose -> error "should not happen"
        
-- Extract the actsfor constraints
toActsFor :: FlameRec -> Ct -> [ActsForCt]
toActsFor flrec ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq af fsk -> maybeToList $ getActsFor af
    IrredPred af -> maybeToList $ getActsFor af
    ClassPred cls afs | isCTupleClass cls -> mapMaybe getActsFor afs 
    _ -> []
  where
    getActsFor af = case af of
                     TyConApp tc [p,q]
                       | tc == (actsfor flrec) -> do
                         sup <- normPrin flrec p
                         inf <- normPrin flrec q
                         return (ct, (sup, inf))
                     af -> Nothing
                         
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
evMagic flrec cts preds = -- pprTrace "Draw" (ppr preds) $ 
  let afscts = mapMaybe (\ct -> case classifyPredType $ ctEvPred $ ctEvidence ct of
                EqPred NomEq af fsk -> Just (af, ct)
                IrredPred af -> Just (af, ct)
                ClassPred cls (af:afs)
                  | isCTupleClass cls -> Just (af,ct) --XXX: HACK: only using first
                _ -> Nothing) cts
  in doMagic afscts
 where
   doMagic :: [(PredType, Ct)] -> TcPluginM ([(EvTerm, Ct)], [Ct])
   doMagic afcts@((af,ct):_) = do
       holes <- replicateM (length preds) newCoercionHole
       --XXX ugh. what ctLoc to use here?
       let newWanted = zipWith (unifyItemToCt (ctLoc ct)) preds holes
           holeEvs   = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes preds
           kprinReflCo = mkNomReflCo $ TyConApp (kprin flrec) []
           kprinCoBndr = (,kprinReflCo) <$> (newFlexiTyVar $  TyConApp (kprin flrec) [])
       evs <- mapM (\(af', ct') -> case af' of
                TyConApp tc [p,q] | tc == (actsfor flrec) -> do
                  let ctEv = mkUnivCo (PluginProv "flame") Representational (mkHEqPred p q) af'
                  forallEv <- mkForAllCos <$> (replicateM (length preds) kprinCoBndr) <*> pure ctEv
                  let finalEv = foldl mkInstCo forallEv holeEvs
                  return $ Just (EvDFunApp (dataConWrapId heqDataCon)
                                [typeKind p, typeKind q, p, q]
                                [evByFiat "flame" p q] `EvCast` finalEv, ct')
                _ -> return Nothing) afcts
       return (catMaybes evs, newWanted)

unifyItemToCt :: CtLoc
              -> PredType
              -> CoercionHole
              -> Ct
unifyItemToCt loc pred_type hole = mkNonCanonical (CtWanted pred_type (HoleDest hole) loc)

mkHEqPred :: Type -> Type -> Type
mkHEqPred t1 t2 = TyConApp heqTyCon [typeKind t1, typeKind t2, t1, t2]
