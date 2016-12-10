{-|
Based heavily on https://github.com/clash-lang/ghc-typelits-natnormalise
by Christiaan Baaij <christiaan.baaij@gmail.com>.
License: BSD2

A type checker plugin for GHC that can solve FLAM acts-for contraints
on types of kind 'Flame.Principals.KPrin'.

To use the plugin, add
@
{\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Normalize \#-\}
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
import Control.Arrow       (second)
import Control.Monad       (replicateM)
import Data.List           (intersect)
import Data.Maybe          (mapMaybe)
import Data.IORef          (IORef, newIORef,readIORef, modifyIORef)

-- GHC API
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (..))
import TcPluginM  (TcPluginM, tcPluginTrace, zonkCt)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred, IrredPred), PredType,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy)

import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar)
import TcRnTypes  (CtEvidence (..), CtLoc, TcEvDest (..), ctLoc)
import TyCoRep    (UnivCoProvenance (..))
import Type       (mkPrimEqPred)
import TcType     (typeKind)
import TyCoRep    (Type (..))
import TcTypeNats (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                   typeNatSubTyCon)

import TcTypeNats (typeNatLeqTyCon)
import Type       (mkNumLitTy,mkTyConApp)
import TysWiredIn (promotedFalseDataCon, promotedTrueDataCon)

-- plugin
import FastString (fsLit)
import GHC.TcPluginM.Extra (evByFiat, lookupModule, lookupName, newGiven, tracePlugin)
import OccName    (mkTcOcc, mkDataOcc, mkClsOcc)
import Module     (mkModuleName)
import TcPluginM  (TcPluginM, tcLookupTyCon, tcLookupDataCon, tcLookupClass, tcPluginIO, tcPluginTrace, zonkCt)
import DataCon (promoteDataCon)
import TysWiredIn (promotedTrueDataCon)

-- internal
import Flame.Solver.Data
import Flame.Solver.Unify
import Flame.Solver.Norm

-- | To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Normalize \#-\}
-- @
--
-- To the header of your file.
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const $ Just normalizePlugin }

normalizePlugin :: TcPlugin
normalizePlugin = tracePlugin "flame"
  TcPlugin { tcPluginInit  = lookupFlameRec
           , tcPluginSolve = decideActsFor
           , tcPluginStop  = \_ -> (return ())
           }

lookupFlameRec :: TcPluginM FlameRec
lookupFlameRec = do
    --discharged <- tcPluginIO $ newIORef []
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
    ,  confClosure = []
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
    let unit_wanteds = mapMaybe (toActsFor flrec) wanteds'
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        unit_givens <- mapMaybe (toGivenActsFor flrec) <$> mapM zonkCt givens
        sr <- simplifyPrins flrec unit_givens unit_wanteds
        tcPluginTrace "flame-normalized" (ppr sr)
        case sr of
          Simplified evs -> do
            let solved = filter (isWanted . ctEvidence . (\((_,x),_) -> x)) evs
                (solved',newWanteds) = second concat (unzip solved)
            return (TcPluginOk solved' newWanteds)
          Impossible eq -> return (TcPluginContradiction [fromActsFor eq])

type ActsForCt = (Ct, (CoreNorm, CoreNorm))

fromActsFor :: ActsForCt -> Ct
fromActsFor (ct, _)    = ct

data SimplifyResult
  = Simplified [((EvTerm,Ct),[Ct])]
  | Impossible ActsForCt

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyPrins :: FlameRec
             -> [ActsForCt]
             -> [ActsForCt]
             -> TcPluginM SimplifyResult
simplifyPrins flrec givens eqs =
    tcPluginTrace "simplifyPrins" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: [CoreUnify]
            -> [((EvTerm, Ct), [Ct])]
            -> [ActsForCt]
            -> [ActsForCt]
            -> TcPluginM SimplifyResult
    simples _subst evs _xs [] = return (Simplified evs)
    simples subst evs xs (eq@(ct,(u,v)):eqs') = do
      -- XXX: this is inefficient. would be better to only recompute
      --      parts of closure that have TyVars that were substituted
      let (conf_givens_flat, integ_givens_flat) =
            flattenDelegations $ map (substsGiven subst) givens
          conf_closure = computeDelClosure conf_givens_flat
          integ_closure = computeDelClosure integ_givens_flat
          flrec' = flrec{confClosure = conf_closure, integClosure = integ_closure}
      ur <- unifyPrins flrec' ct (substsNorm subst u) (substsNorm subst v)
      tcPluginTrace "unifyPrins result" (ppr ur)
      case ur of
        Win -> do
          evs' <- maybe evs (:evs) <$> evMagic flrec' ct []
          simples subst evs' [] (xs ++ eqs')
        Lose -> return (Impossible eq)
        Draw [] -> simples subst evs (eq:xs) eqs'
        Draw subst' -> do
          evM <- evMagic flrec' ct (map (unifyItemToPredType flrec') subst')
          case evM of
            Nothing -> simples subst evs xs eqs'
            Just ev ->
              simples (substsSubst subst' subst ++ subst')
                      (ev:evs) [] (xs ++ eqs')
    substsGiven s (ct, (p, q)) = (substsNorm s p, substsNorm s q) 

-- Extract the given
toGivenActsFor :: FlameRec -> Ct -> Maybe ActsForCt
toGivenActsFor flrec ct =
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq af fsk -> 
                   case af of
                     TyConApp tc [p,q]
                       | tc == (actsfor flrec) -> 
                         let sup = normPrin flrec p in
                         let inf = normPrin flrec q in
                            Just (ct, (sup, inf))
                     _ -> Nothing
    _ -> Nothing
-- Extract the acts-for constraints
toActsFor :: FlameRec -> Ct -> Maybe ActsForCt
toActsFor flrec ct =
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    IrredPred af -> case af of
                     TyConApp tc [p,q]
                       | tc == (actsfor flrec) -> 
                         let sup = normPrin flrec p in
                         let inf = normPrin flrec q in
                            --(pprTrace "wanted" (ppr (sup, inf)) $
                             Just (ct, (sup, inf))
                     _ -> Nothing
    -- TODO: Support (propositional?) equality constraints on principals
    _ -> Nothing

unifyItemToPredType :: FlameRec -> CoreUnify -> PredType
unifyItemToPredType flrec ui =
    mkPrimEqPred ty1 ty2
  where
    ty1 = case ui of
            SubstItem {..} -> mkTyVarTy siVar
            UnifyItem {..} -> reifyNorm flrec siLHS
    ty2 = case ui of
            SubstItem {..} -> reifyNorm flrec siNorm
            UnifyItem {..} -> reifyNorm flrec siRHS

evMagic :: FlameRec -> Ct -> [PredType] -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
evMagic flrec ct preds = case classifyPredType $ ctEvPred $ ctEvidence ct of
  IrredPred af ->
    case af of
     TyConApp tc [p,q] | tc == (actsfor flrec) -> do
       holes <- replicateM (length preds) newCoercionHole
       let newWanted = zipWith (unifyItemToCt (ctLoc ct)) preds holes
           ctEv      = mkUnivCo (PluginProv "flame") Nominal p q 
           holeEvs   = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes preds
           natReflCo = mkNomReflCo $ TyConApp (kprin flrec) []
           natCoBndr = (,natReflCo) <$> (newFlexiTyVar $  TyConApp (kprin flrec) [])
       forallEv <- mkForAllCos <$> (replicateM (length preds) natCoBndr) <*> pure ctEv
       let finalEv = foldl mkInstCo forallEv holeEvs
       return (Just ((EvCoercion finalEv, ct),newWanted))
     _ -> return Nothing
  _ -> return Nothing

unifyItemToCt :: CtLoc
              -> PredType
              -> CoercionHole
              -> Ct
unifyItemToCt loc pred_type hole = mkNonCanonical (CtWanted pred_type (HoleDest hole) loc)
