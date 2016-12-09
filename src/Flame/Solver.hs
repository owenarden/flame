{-# LANGUAGE CPP             #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Flame.Solver
  ( plugin )
where

-- External
import Data.List     
import Control.Arrow       ((***))
import Data.List           (partition)
import Data.Maybe          (mapMaybe)
import Data.Graph 
import GHC.TcPluginM.Extra (evByFiat, lookupModule, lookupName, newGiven)
import Data.IORef          (IORef, newIORef,readIORef, modifyIORef)
import Data.Either (partitionEithers)
import Data.List   (sort)
import System.IO.Unsafe
import Debug.Trace (trace)
import Control.Monad       (replicateM)

-- GHC API
import FastString (fsLit)
import Outputable  (Outputable (..), (<+>), text, hcat, integer, punctuate, ppr, pprTrace)
import Module     (mkModuleName)
import OccName    (mkTcOcc, mkDataOcc, mkClsOcc)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm)
import TcPluginM  (TcPluginM, tcLookupTyCon, tcLookupDataCon, tcLookupClass, tcPluginIO, tcPluginTrace, zonkCt)

import TcRnTypes  (Ct, CtEvidence, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   ctPred, ctLoc, isGiven, isWanted, mkNonCanonical)
import TyCon      (TyCon)
import Class      (Class)
import Var        (isTcTyVar, isTyVar)
import TcType     (isSkolemTyVar)
import Type       (EqRel (..), Kind, PredTree (..), PredType, Type, TyVar, splitTyConApp_maybe,
                   classifyPredType, coreView, getEqPredTys, mkTyVarTy, mkTyConApp, mkTyVarTy)


import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (..))
import TcPluginM  (TcPluginM, tcPluginTrace, zonkCt)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy)
import TysWiredIn (typeNatKind)

import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar)
import TcRnTypes  (CtEvidence (..), CtLoc, TcEvDest (..), ctLoc)
import Type       (mkPrimEqPred)
import TcType     (typeKind)
       
#if __GLASGOW_HASKELL__ >= 711
import TyCoRep    (Type (..), TyLit (..))
#else
import TypeRep    (Type (..), TyLit (..))
#endif
import DataCon (promoteDataCon)
import TysWiredIn (promotedTrueDataCon)
import Coercion   (Role (..), mkUnivCo)
#if __GLASGOW_HASKELL__ >= 711
import TcEvidence (EvTerm (..))
#else
import TcEvidence (EvTerm (..), TcCoercion (..))
import TcMType    (newEvVar)
#endif
import UniqSet       (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                      unitUniqSet)
  
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = \_ -> Just flamePlugin }

flamePlugin :: TcPlugin
flamePlugin =
  TcPlugin { tcPluginInit  = lookupFlameRec
           , tcPluginSolve = decideActsFor
           , tcPluginStop  = \_ -> return ()
           }

type DelClosure = [(CoreJNorm, [CoreJNorm])]
data FlameRec = FlameRec {
   discharged   :: IORef [Ct],
   ktop         :: TyCon, 
   kbot         :: TyCon, 
   kname        :: TyCon, 
   kconj        :: TyCon, 
   kdisj        :: TyCon, 
   kconf        :: TyCon, 
   kinteg       :: TyCon,
   kvoice       :: TyCon,
   keye         :: TyCon,
   actsfor      :: TyCon,
   confClosure  :: DelClosure,
   integClosure :: DelClosure
 }

lookupFlameRec :: TcPluginM FlameRec
lookupFlameRec = do
    discharged <- tcPluginIO $ newIORef []
    md         <- lookupModule flameModule flamePackage
    ktopDataNm   <- lookupName md (mkDataOcc "KTop")
    kbotDataNm   <- lookupName md (mkDataOcc "KBot")
    knameDataNm  <- lookupName md (mkDataOcc "KName")
    kconjDataNm  <- lookupName md (mkDataOcc "KConj")
    kdisjDataNm  <- lookupName md (mkDataOcc "KDisj")
    kconfDataNm  <- lookupName md (mkDataOcc "KConf")
    kintegDataNm <- lookupName md (mkDataOcc "KInteg")
    kvoiceDataNm <- lookupName md (mkDataOcc "KVoice")
    keyeDataNm <- lookupName md (mkDataOcc "KEye")
    actsforNm    <- lookupName md (mkTcOcc "≽")
    ktopTc   <- promoteDataCon <$> tcLookupDataCon ktopDataNm
    kbotTc   <- promoteDataCon <$> tcLookupDataCon kbotDataNm
    knameTc  <- promoteDataCon <$> tcLookupDataCon knameDataNm
    kconjTc  <- promoteDataCon <$> tcLookupDataCon kconjDataNm
    kdisjTc  <- promoteDataCon <$> tcLookupDataCon kdisjDataNm
    kconfTc  <- promoteDataCon <$> tcLookupDataCon kconfDataNm
    kintegTc <- promoteDataCon <$> tcLookupDataCon kintegDataNm
    kvoiceTc <- promoteDataCon <$> tcLookupDataCon kvoiceDataNm
    keyeTc   <- promoteDataCon <$> tcLookupDataCon keyeDataNm
    actsforTc  <-  tcLookupTyCon actsforNm
    return FlameRec{
       ktop       = ktopTc
    ,  kbot       = kbotTc
    ,  kname      = knameTc
    ,  kconj      = kconjTc
    ,  kdisj      = kdisjTc
    ,  kconf      = kconfTc
    ,  kinteg     = kintegTc
    ,  kvoice     = kvoiceTc
    ,  keye       = keyeTc
    ,  actsfor    = actsforTc
    ,  confClosure = []
    ,  integClosure = []
    }
  where
    flameModule  = mkModuleName "Flame.Principals"
    flamePackage = fsLit "flame"

data SimplifyResult
  = Simplified [(EvTerm,Ct,(CoreNorm, CoreNorm))]
  | Impossible (CoreNorm, CoreNorm)

decideActsFor :: FlameRec
                     -> [Ct] -- ^ [G]iven constraints
                     -> [Ct] -- ^ [D]erived constraints
                     -> [Ct] -- ^ [W]anted constraints
                     -> TcPluginM TcPluginResult
decideActsFor _ _ _ [] = return (TcPluginOk [] []) 
decideActsFor flrec given derived wanteds = return $! case failed of
 --   [] -> TcPluginOk (mapMaybe (\c -> (,c) <$> evMagic flrec c) solved) []
 --   f  -> TcPluginContradiction f
    -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
    case afWanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        tcPluginTrace "flame" (ppr "foo")
        case simplifyActsFor afWanted of
          [] -> TcPluginOk (mapMaybe (\c -> (,c) <$> evMagic flrec c) solved) []
          Simplified subst evs -> do
            let solved     = filter (isWanted . ctEvidence . (\(_,x,_) -> x)) evs
            dischargedWanteds <- tcPluginIO (readIORef (discharged flrec))
            let existingWanteds = wanteds' ++ dischargedWanteds
            -- Create new wanted constraints
            (solved',newWanteds) <- (second concat . unzip . catMaybes) <$>
                                    mapM (evItemToCt existingWanteds) solved
            -- update set of discharged wanteds
            tcPluginIO (modifyIORef (discharged flrec) (++ newWanteds))
            -- return
            return (TcPluginOk solved' newWanteds)
          Impossible (ct, _ ) -> failWithProvenace ct
  where

    afGivens :: [(CoreNorm,CoreNorm)]
    afGivens = mapMaybe (toGiven flrec) <$> mapM zonkCt given 
    (confExp, integExp) = expandGivens $ pprTrace "given" (ppr afGivens) afGivens

    confClosure :: [(CoreJNorm, [CoreJNorm])]
    confClosure = givenClosure confExp 

    integClosure :: [(CoreJNorm, [CoreJNorm])]
    integClosure = givenClosure integExp 

    afWanteds :: [(Ct,(CoreNorm,CoreNorm))]
    afWanteds = mapMaybe (toActsFor flrec) wanteds

    variables = unionManyUniqSets [ fvNorm sup | (ct, (sup, inf)) <- afWanteds]

    flrec' = flrec{confClosure = confClosure,
                   integClosure = --pprTrace "integ closure" (ppr integClosure)
                                  integClosure}

    simplifyActsFor :: SimplifyResult
    simplifyActsFor = foldl (\res (ct, (sup, inf)) ->
                        case res of
                          Impossible _ -> res
                          Simplified evs ->
                            case actsFor flrec' (sup, inf) of
                            Just pf -> pprTrace "proof" (ppr pf)
                                       evs
                            Nothing -> pprTrace "failed" (ppr (sup, inf)) $
                                       {- no type variables in superior, nothing we can do -}
                                       if fvNorm sup == emptyUniqSet then
                                         Impossible (ct, (sup, inf))
                                       else


--     solved, failed :: [(Ct, (CoreNorm, CoreNorm))]
--     (solved,failed) = --(map fst *** map fst) $
--                       partition (\(ct, (sup, inf)) ->
--                                     case actsFor flrec' (sup, inf) of
--                                     Just pf -> --pprTrace "proof" (ppr pf)
--                                                True
--                                     Nothing -> pprTrace "failed" (ppr (sup, inf)) $
--                                                --if fvNorm sup == emptyUniqSet then
--                                                  False
--                                                --else
--                                                  
--                                   )
--                         (pprTrace "wanted" (ppr afWanteds) $ 
--                          pprTrace "fvs" (ppr variables) $ afWanteds)
simplifyNats :: [Either NatEquality NatInEquality]
             -> TcPluginM SimplifyResult
simplifyNats eqs =
    tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: CoreUnify CoreNote
            -> [Maybe (EvTerm, Ct, CoreUnify CoreNote)]
            -> [Either NatEquality NatInEquality]
            -> [Either NatEquality NatInEquality]
            -> TcPluginM SimplifyResult
    simples subst evs _xs [] = return (Simplified subst (catMaybes evs))
    simples subst evs xs (eq@(Left (ct,u,v)):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win         -> simples subst (((,,) <$> evMagic ct <*> pure ct <*> pure []):evs) []
                               (xs ++ eqs')
        Lose        -> return (Impossible eq)
        Draw []     -> simples subst evs (eq:xs) eqs'
        Draw subst' -> do
          simples (substsSubst subst' subst ++ subst')
                  (((,,) <$> evMagic ct <*> pure ct <*> pure subst'):evs)
                  [] (xs ++ eqs')
{-
-}
{-- stolen from ghc-typelits-natnormalise -}
unifyNormToPredType :: FlameRec -> CoreNorm -> CoreNorm -> PredType
unifyNormToPredType flrec =
    mkPrimEqPred (reifyNorm flrec p) (reifyNorm flrec q)

evItemToCt :: [Ct] -- ^ Existing wanteds
           -> (EvTerm,Ct,CoreUnify CoreNote)
           -> TcPluginM (Maybe ((EvTerm,Ct),[Ct]))
evItemToCt existingWanteds (ev,ct,subst)
    | null newWanteds = return (Just ((ev,ct),[]))
    | otherwise = do
        newWanteds' <- catMaybes <$> mapM (substItemToCt existingWanteds) newWanteds
        -- only allow new (conditional) evidence if conditional wanted constraints
        -- can be added as new work
        if length newWanteds == length newWanteds'
           then return (Just ((ev,ct),newWanteds'))
           else return Nothing
  where
#if __GLASGOW_HASKELL__ >= 711
    newWanteds = filter (isWanted . ctEvidence . snd . siNote) subst
#else
    newWanteds = filter (isWanted . ctEvidence . siNote) subst
#endif

substItemToCt :: [Ct] -- ^ Existing wanteds wanted
              -> UnifyItem TyVar Type CoreNote
              -> TcPluginM (Maybe Ct)
substItemToCt existingWanteds si
  | predicate  `notElem` wantedPreds
  , predicateS `notElem` wantedPreds
#if __GLASGOW_HASKELL__ >= 711
  = return (Just (mkNonCanonical (CtWanted predicate (HoleDest ev) (ctLoc ct))))
#else
  = Just <$> mkNonCanonical <$> newWantedWithProvenance (ctEvidence ct) predicate
#endif
  | otherwise
  = return Nothing
  where
    predicate   = unifyItemToPredType si
    (ty1,ty2)   = getEqPredTys predicate
#if __GLASGOW_HASKELL__ >= 711
    predicateS    = mkPrimEqPred ty2 ty1
    ((ev,_,_),ct) = siNote si
#else
    predicateS  = mkEqPred ty2 ty1
    ct          = siNote si
#endif
    wantedPreds = map ctPred existingWanteds
    
evMagic :: Ct -> [PredType] -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
evMagic ct preds = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 -> do
    holes <- replicateM (length preds) newCoercionHole
    let newWanted = zipWith (unifyNormToCt (ctLoc ct)) preds holes
        ctEv      = mkUnivCo (PluginProv "flame") Nominal t1 t2
        holeEvs   = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes preds
        natReflCo = mkNomReflCo typeNatKind
        natCoBndr = (,natReflCo) <$> (newFlexiTyVar typeNatKind)
    forallEv <- mkForAllCos <$> (replicateM (length preds) natCoBndr) <*> pure ctEv
    let finalEv = foldl mkInstCo forallEv holeEvs
    return (Just ((EvCoercion finalEv, ct),newWanted))
  _ -> return Nothing

unifyNormToCt :: CtLoc
              -> PredType
              -> CoercionHole
              -> Ct
unifyNormToCt loc pred_type hole = mkNonCanonical (CtWanted pred_type (HoleDest hole) loc)

toGiven :: FlameRec -> Ct -> Maybe (CoreNorm, CoreNorm)
toGiven flrec ct =
  case classifyPredType (ctPred ct) of
    EqPred NomEq af fsk -> 
                   case af of
                     TyConApp tc [p,q]
                       | tc == (actsfor flrec) -> 
                         let sup = normPrin flrec p in
                         let inf = normPrin flrec q in
                            Just (sup, inf)
                     _ -> Nothing
    _ -> Nothing

toActsFor :: FlameRec -> Ct -> Maybe (Ct,(CoreNorm,CoreNorm))
toActsFor flrec ct =
  case classifyPredType (ctPred ct) of
    IrredPred af -> 
                   case af of
                     TyConApp tc [p,q]
                       | tc == (actsfor flrec) -> 
                         let sup = normPrin flrec p in
                         let inf = normPrin flrec q in
                            --(pprTrace "wanted" (ppr (sup, inf)) $
                             Just (ct, (sup, inf))
                     _ -> Nothing
    _ -> Nothing

evMagic :: FlameRec -> Ct -> Maybe EvTerm
evMagic flrec ct = 
    case classifyPredType (ctPred ct) of
      IrredPred af -> 
                   case af of
                     TyConApp tc [p,q]
                       | tc == (actsfor flrec) -> 
                         Just (evByFiat "flame" p q)
                     _ -> Nothing
      _ -> Nothing

