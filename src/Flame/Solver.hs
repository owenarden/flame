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
import Control.Arrow       (second)
import Control.Monad       (replicateM)
import Data.Maybe          (mapMaybe, maybeToList)

-- GHC API
import Outputable (Outputable (..), (<+>), ($$), text, ppr, pprTrace)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvTerm (..))
import TcPluginM  (TcPluginM, tcPluginTrace, zonkCt, tcLookupTyCon, tcLookupDataCon,
                   tcPluginIO)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred, IrredPred, ClassPred), PredType,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy, mkPrimEqPred, isCTupleClass, typeKind)
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
    let unit_wanteds = concat $ map (toActsFor flrec) wanteds'
    -- XXX: natnormalise zonkCt's these, but that appears to remove the ones I care about.
    let unit_givens = concat $ map (toActsFor flrec) givens
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        --unit_givens <- concat <$> mapM (toActsFor flrec) <$> mapM zonkCt givens
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

-- TODO: need to change from evs to "sovled" cts, then generate evidence all at once.
simplifyPrins :: FlameRec
             -> [ActsForCt]
             -> [ActsForCt]
             -> TcPluginM SimplifyResult
simplifyPrins _flrec givens eqs =
    tcPluginTrace "simplifyPrins" (ppr eqs) >> simples _flrec [] [] [] eqs
  where
    simples :: FlameRec
            -> [((EvTerm, Ct), [Ct])]
            -> [ActsForCt]
            -> [ActsForCt]
            -> TcPluginM SimplifyResult
    simples _flrec evs _xs [] = do
      evM <- evMagic flrec' ct $ boundsToPredTypes _flrec 
      case evM of
        Nothing -> return (Simplified ev)
        Just ev -> return (Simplified (ev:evs))
    simples flrec evs xs (eq@(ct,(u,v)):eqs') = do
      -- XXX: this is inefficient. would be better to only recompute
      --      parts of closure that have TyVars that were substituted
      -- UPDATE: maybe don't need to do this in the loop anymore!
      --         vars are only substituted in actsfor given a set of bounds.
      --      BUT: what about structural superiors?
      let (conf_givens_flat, integ_givens_flat) = flattenDelegations givens
          conf_closure =  computeDelClosure conf_givens_flat
          integ_closure = computeDelClosure integ_givens_flat
          flrec' = flrec{confClosure = conf_closure, integClosure = integ_closure}
      -- TODO: solve on uninstantiated vars. return updated bounds
      ur <- solvePrins flrec' ct u v
      tcPluginTrace "solvePrins result" (ppr ur)
      case ur of
        Win -> do
          evs' <- maybe evs (:evs) <$> evMagic flrec' ct []
          simples evs' [] (xs ++ eqs')
        Lose -> return (Impossible eq)
        -- Draw [] -> simples subst evs (eq:xs) eqs'
        Draw (cbnds, ibnds) -> do
                        simples (substsSubst subst' subst ++ subst')
                      (ev:evs) [] (xs ++ eqs')
    substsGiven s (ct, (p, q)) = (substsNorm s p, substsNorm s q) 

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
                         
boundsToPredTypes :: CoreBounds -> [PredType]
boundsToPredTypes flrec =
    mkPrimEqPred ty1 ty2
  where
    ty1 = case ui of
            SubstItem {..} -> mkTyVarTy siVar
            UnifyItem {..} -> reifyNorm flrec siLHS
    ty2 = case ui of
            SubstItem {..} -> reifyNorm flrec siNorm
            UnifyItem {..} -> reifyNorm flrec siRHS

evMagic :: FlameRec -> Ct -> [PredType] -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
evMagic flrec ct preds = -- pprTrace "Draw" (ppr preds) $ 
 case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq af fsk -> --pprTrace "EQ PRED: " ((ppr af) <+> (ppr fsk)) $
    doEQMagic af
  IrredPred af -> -- pprTrace "IRRED PRED: " ((ppr ct) <+> (ppr af) <+> (ppr preds)) $
    doEQMagic af
  ClassPred cls (af:afs) | isCTupleClass cls -> doEQMagic af -- XXX: HACK: only using first one..
                                                             -- Still don't understand how evidence terms are used.
  _ -> return Nothing
 where
   --doEQMagic af = case af of
   --  -- This is based on Adam Gundry's uom-plugin. Ignoring newWanted for now.
   --  TyConApp tc [p,q] | tc == (actsfor flrec) ->
   --     -- return $ (Just ((mkActsForEvidence af p q, ct), newWanted))
   --  _ -> return Nothing
   doEQMagic af = case af of
     TyConApp tc [p,q] | tc == (actsfor flrec) -> do
       holes <- replicateM (length preds) newCoercionHole
       let newWanted = zipWith (unifyItemToCt (ctLoc ct)) preds holes
           ctEv      = mkUnivCo (PluginProv "flame") Representational (mkHEqPred p q) af
           holeEvs   = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes preds
           natReflCo = mkNomReflCo $ TyConApp (kprin flrec) []
           natCoBndr = (,natReflCo) <$> (newFlexiTyVar $  TyConApp (kprin flrec) [])
       forallEv <- mkForAllCos <$> (replicateM (length preds) natCoBndr) <*> pure ctEv
       let finalEv = foldl mkInstCo forallEv holeEvs
       return (Just ((EvDFunApp (dataConWrapId heqDataCon) [typeKind p, typeKind q, p, q] [evByFiat "flame" p q] `EvCast` finalEv, ct), newWanted))
     _ -> return Nothing


-- | Make up evidence for a fake equality constraint @t1 ~~ t2@ by
-- coercing bogus evidence of type @t1 ~ t2@ (or its heterogeneous
-- variant, in GHC 8.0).
-- stolen from https://github.com/adamgundry/uom-plugin
--mkActsForEvidence :: Type -> Type -> Type -> EvTerm
--mkActsForEvidence af p q = EvDFunApp (dataConWrapId heqDataCon) [typeKind p, typeKind q, p, q] [evByFiat "flame" p q]
--                       `EvCast` mkUnivCo (PluginProv "flame") Representational (mkHEqPred p q) af
 
unifyItemToCt :: CtLoc
              -> PredType
              -> CoercionHole
              -> Ct
unifyItemToCt loc pred_type hole = mkNonCanonical (CtWanted pred_type (HoleDest hole) loc)

mkHEqPred :: Type -> Type -> Type
mkHEqPred t1 t2 = TyConApp heqTyCon [typeKind t1, typeKind t2, t1, t2]
