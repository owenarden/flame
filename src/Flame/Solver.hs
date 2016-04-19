{-# LANGUAGE CPP             #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Flame.Solver
  ( plugin )
where

-- External
import Data.Function (on)
import Data.List     
import Control.Arrow       ((***))
import Data.List           (partition)
import Data.Maybe          (mapMaybe)
import Data.Graph 
import GHC.TcPluginM.Extra (evByFiat, lookupModule, lookupName, newGiven)
import Data.IORef          (IORef, newIORef,readIORef, modifyIORef)

import System.IO.Unsafe
import Debug.Trace (trace)
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
import Type       (EqRel (..), Kind, PredTree (..), PredType, Type, TyVar, splitTyConApp_maybe,
                   classifyPredType, coreView, getEqPredTys, mkTyVarTy, mkTyConApp, mkTyVarTy)
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
 

import GHC.Extra.Instances () -- Ord instance for Type

-- Internal
import Flame.Normalize
import Test.QuickCheck

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = \_ -> Just flamePlugin }

flamePlugin :: TcPlugin
flamePlugin =
  TcPlugin { tcPluginInit  = lookupFlameRec
           , tcPluginSolve = decideActsFor
           , tcPluginStop  = \_ -> return ()
           }

type DelClosure = [(CoreBase, [CoreBase])]
data FlameRec = FlameRec {
                       ktop         :: TyCon, 
                       kbot         :: TyCon, 
                       kname        :: TyCon, 
                       kconj        :: TyCon, 
                       kdisj        :: TyCon, 
                       kconf        :: TyCon, 
                       kinteg       :: TyCon,
                       actsfor      :: TyCon,
                       confClosure  :: DelClosure,
                       integClosure :: DelClosure
                     }

lookupFlameRec :: TcPluginM FlameRec
lookupFlameRec = do
    md         <- lookupModule flameModule flamePackage
    ktopDataNm   <- lookupName md (mkDataOcc "KTop")
    kbotDataNm   <- lookupName md (mkDataOcc "KBot")
    knameDataNm  <- lookupName md (mkDataOcc "KName")
    kconjDataNm  <- lookupName md (mkDataOcc "KConj")
    kdisjDataNm  <- lookupName md (mkDataOcc "KDisj")
    kconfDataNm  <- lookupName md (mkDataOcc "KConf")
    kintegDataNm <- lookupName md (mkDataOcc "KInteg")
    actsforNm  <- lookupName md (mkTcOcc "≽")
    ktopTc   <- promoteDataCon <$> tcLookupDataCon ktopDataNm
    kbotTc   <- promoteDataCon <$> tcLookupDataCon kbotDataNm
    knameTc  <- promoteDataCon <$> tcLookupDataCon knameDataNm
    kconjTc  <- promoteDataCon <$> tcLookupDataCon kconjDataNm
    kdisjTc  <- promoteDataCon <$> tcLookupDataCon kdisjDataNm
    kconfTc  <- promoteDataCon <$> tcLookupDataCon kconfDataNm
    kintegTc <- promoteDataCon <$> tcLookupDataCon kintegDataNm
    actsforTc  <-  tcLookupTyCon actsforNm
    return FlameRec{
       ktop       = ktopTc
    ,  kbot       = kbotTc
    ,  kname      = knameTc
    ,  kconj      = kconjTc
    ,  kdisj      = kdisjTc
    ,  kconf      = kconfTc
    ,  kinteg     = kintegTc
    ,  actsfor    = actsforTc
    ,  confClosure = []
    ,  integClosure = []
    }
  where
    flameModule  = mkModuleName "Flame.Principals"
    flamePackage = fsLit "flame"

-- | 'Norm' with 'TyVar' variables
type CoreNorm   = Norm TyVar Type
type CoreJNorm  = JNorm TyVar Type
type CoreMNorm  = MNorm TyVar Type
type CoreBase   = Base TyVar Type

-- | Convert a type of /kind/ 'Flame.Principals.KPrin' to a 'JNorm' term
--
-- flrec contains the KPrin type constructors
-- cproj indicates whether we are normalizing the conf component
jnormPrin :: FlameRec -> Bool -> Type -> CoreJNorm
jnormPrin flrec cproj ty | Just ty1 <- coreView ty = jnormPrin' ty1
  where jnormPrin' = jnormPrin flrec cproj
jnormPrin flrec cproj (TyVarTy v) = J [M [V v]]
jnormPrin flrec cproj (TyConApp tc [])
  | tc == (ktop flrec) = J [M [T]]
  | tc == (kbot flrec) = J [M [B]]
jnormPrin flrec cproj (TyConApp tc [x])
  | tc == (kname flrec) = J [M [P x]]
  | tc == (kconf flrec) =
    if cproj then jnormPrin' x else J [M [B]]
  | tc == (kinteg flrec) = 
    if cproj then J [M [B]] else jnormPrin' x
  where jnormPrin' = jnormPrin flrec cproj
jnormPrin flrec cproj (TyConApp tc [x,y])
  | tc == (kconj flrec) = mergeJNormJoin (jnormPrin' x) (jnormPrin' y)
  | tc == (kdisj flrec) = mergeJNormMeet (jnormPrin' x) (jnormPrin' y)
  where jnormPrin' = jnormPrin flrec cproj
jnormPrin flrec cproj t = J [M [P t]]

-- | Convert a type of /kind/ 'Flame.Principals.KPrin' to a 'JNorm' term
normPrin :: FlameRec -> Type -> Maybe CoreNorm
normPrin flrec ty
  | Just ty1 <- coreView ty =
      Just (N (jnormPrin flrec True ty1) (jnormPrin flrec False ty1))
normPrin flrec (TyVarTy v) = Just (N (J [M [V v]]) (J [M [V v]]))
normPrin flrec (TyConApp tc [])
  | tc == (ktop flrec) = Just (N (J [M [T]]) (J [M [T]]))
  | tc == (kbot flrec) = Just (N (J [M [B]]) (J [M [B]]))
normPrin flrec (TyConApp tc [x])
  | tc == (kname flrec) =  Just (N (J [M [P x]]) (J [M [P x]]))
  | tc == (kconf flrec) =  Just (N (jnormPrin flrec True x) (J [M [B]]))
  | tc == (kinteg flrec) = Just (N (J [M [B]]) (jnormPrin flrec False x))
normPrin flrec (TyConApp tc [x,y])
  | tc == (kconj flrec) = do x' <- normPrin flrec x
                             y' <- normPrin flrec y
                             Just (mergeNormJoin x' y')
  | tc == (kdisj flrec) = do x' <- normPrin flrec x;
                             y' <- normPrin flrec y;
                             Just (mergeNormMeet x' y')
normPrin flrec _ = Nothing

-- | Convert a 'SOP' term back to a type of /kind/ 'GHC.TypeLits.Nat'
reifyNorm :: FlameRec -> CoreNorm -> Type
reifyNorm flrec (N (J cms) (J ims)) =
  let c' = combineM cms in
  let i' = combineM ims in
    mkTyConApp (kconj flrec)
      [mkTyConApp (kconf flrec) [c'],
       mkTyConApp (kinteg flrec) [i']]
  where
    combineM :: [CoreMNorm] -> Type
    combineM []     = mkTyConApp (kbot flrec) []
    combineM [p]    = reifyMNorm flrec p
    combineM (p:ps) = let es = combineM ps
                      in mkTyConApp (kconj flrec) [reifyMNorm flrec p, es]

reifyMNorm :: FlameRec -> CoreMNorm -> Type
reifyMNorm flrec = foldr1 (\t1 t2 -> mkTyConApp (kdisj flrec) [t1,t2])
             . map (reifyBase flrec) . unM

reifyBase :: FlameRec -> CoreBase -> Type
reifyBase flrec (V v)   = mkTyVarTy v
reifyBase flrec (P s)   = mkTyConApp (kname flrec) [s]
reifyBase flrec B       = mkTyConApp (kbot flrec) []
reifyBase flrec T       = mkTyConApp (ktop flrec) []

decideActsFor :: FlameRec
                     -> [Ct] -- ^ [G]iven constraints
                     -> [Ct] -- ^ [D]erived constraints
                     -> [Ct] -- ^ [W]anted constraints
                     -> TcPluginM TcPluginResult
decideActsFor _ _ _ [] = return (TcPluginOk [] []) 
decideActsFor flrec given derived wanteds = return $! case (pprTrace "failed" (ppr failed) failed) of
    [] -> TcPluginOk (mapMaybe (\c -> (,c) <$> evMagic flrec c) solved) []
    f  -> TcPluginContradiction f
  where

    afGivens :: [(CoreNorm,CoreNorm)]
    afGivens = mapMaybe (toGiven flrec) given

    (confExp,integExp) = expandGivens afGivens

    confClosure :: [(CoreBase, [CoreBase])]
    confClosure = givenClosure confExp 

    integClosure :: [(CoreBase, [CoreBase])]
    integClosure = givenClosure integExp 

    afWanteds :: [(Ct,(CoreNorm,CoreNorm))]
    afWanteds = mapMaybe (toActsFor flrec) wanteds

    flrec' = flrec{confClosure = confClosure, integClosure = integClosure}

    solved, failed :: [Ct]
    (solved,failed) = (map fst *** map fst)
                      $ partition (\a ->
                                    case actsFor flrec' (snd a) of
                                    Just pf -> (pprTrace "proof" (ppr pf) True)
                                    _       -> False
                                  )
                        afWanteds

expandGivens :: [(CoreNorm,CoreNorm)]
             -> ([(CoreBase,CoreBase)], [(CoreBase,CoreBase)])
expandGivens givens = unzip $ map
                        (\given ->
                          case given of
                            -- TODO: This fails on givens that aren't already in base form
                            (N (J [M [supC]]) (J [M [supI]]), 
                             N (J [M [infC]]) (J [M [infI]])) -> 
                              ((supC, infC), (supI, infI)))
                        givens
  
  -- TODO: expand given constraints to base form

givenClosure :: [(CoreBase,CoreBase)] -> [(CoreBase, [CoreBase])]
givenClosure givens = 
    map (\q -> (q, case prinToVtx q of
                   Just vtx -> map vtxToPrin $ reachable graph vtx))
        principals
  where
    principals :: [CoreBase]
    principals = [T, B] ++ (map head . group . sort $ (map inferior givens ++ map superior givens))

    edges :: [(CoreBase, CoreBase, [CoreBase])]
    edges =  map (\inf ->
                   (inf, inf, [superior af | af  <- givens, inferior af == inf]))
                 principals
    (graph, vtxToEdges, prinToVtx) = graphFromEdges edges

    vtxToPrin :: Vertex -> CoreBase
    vtxToPrin v = let (x, _, _) = vtxToEdges v in x

    inferior :: (CoreBase,CoreBase) -> CoreBase
    inferior = snd

    superior :: (CoreBase,CoreBase) -> CoreBase
    superior = fst
    

toGiven :: FlameRec -> Ct -> Maybe (CoreNorm, CoreNorm)
toGiven flrec ct =
  case classifyPredType (ctPred ct) of
    EqPred NomEq af fsk -> 
                   case af of
                     TyConApp tc [p,q]
                       | tc == (actsfor flrec) -> 
                         do sup <- normPrin flrec p 
                            inf <- normPrin flrec q
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
                         do sup <- normPrin flrec p 
                            inf <- normPrin flrec q
                            (pprTrace "wanted" (ppr (sup, inf)) $
                             (Just (ct, (sup, inf))))
                     _ -> Nothing
    _ -> Nothing

data ActsForProof =                    
      AFTop
    | AFBot
    | AFRefl 
    | AFDel (CoreBase, CoreBase) -- NB: this implicitly uses transitivity on given dels
    | AFConj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFDisj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 

instance Outputable ActsForProof where
    ppr AFTop = text "AFTop"
    ppr AFBot = text "AFBot"
    ppr AFRefl = text "AFRefl"
    ppr (AFDel del) = text "AFDel" <+> ppr del
    ppr (AFConj pfs) = text "AFConj" <+> ppr pfs
    ppr (AFDisj pfs) = text "AFDisj" <+> ppr pfs

actsFor :: FlameRec ->
           (CoreNorm, CoreNorm) ->
           Maybe ActsForProof
actsFor flrec (p,q) 
  | p == top = Just AFTop
  | q == bot = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = 
        do
          confPf <- confActsFor (conf p, conf q)
          integPf <- integActsFor (integ p, integ q)
          Just $ AFConj [confPf, integPf]
  where
    top :: CoreNorm
    top = N (J [M [T]]) (J [M [T]])
    bot :: CoreNorm
    bot = N (J [M [B]]) (J [M [B]])

    confActsFor :: (CoreJNorm, CoreJNorm) -> Maybe ActsForProof
    confActsFor = actsForJ (confClosure flrec)
    integActsFor :: (CoreJNorm, CoreJNorm) -> Maybe ActsForProof
    integActsFor = actsForJ (integClosure flrec)

actsForJ :: DelClosure ->
            (CoreJNorm, CoreJNorm) ->
            Maybe ActsForProof
actsForJ delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = AFConj <$> conjProofs 
  where
    top :: CoreJNorm
    top = J [M [T]]
    bot :: CoreJNorm
    bot = J [M [B]] 
    -- for every join comp on rhs, find sup on lhs
    (J pms, J qms) = (p,q)
    conjProofs :: Maybe [ActsForProof]
    conjProofs = sequence $ map (\qm ->
                                  case map (\pm ->
                                          actsForM delClosure (pm,qm))
                                        pms of
                                    (pf:pfs) -> pf
                                    _ -> Nothing
                                )
                                qms

actsForM :: DelClosure ->
            (CoreMNorm, CoreMNorm) ->
            Maybe ActsForProof
actsForM delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = AFDisj <$> disjProofs
  where
    top :: CoreMNorm
    top = M [T]
    bot :: CoreMNorm
    bot = M [B] 
    -- for every meet comp on lhs, find inf on rhs
    (M pbs, M qbs) = (p,q)
    disjProofs :: Maybe [ActsForProof]
    disjProofs = sequence $ map (\pb ->
                                  case map (\qb ->
                                          actsForB delClosure (pb,qb))
                                        qbs of
                                    (pf:pfs) -> pf
                                    _ -> Nothing
                                )
                                pbs
-- IDEA for transitivity.  If all given dels are expressed "primitively", then transitivity can be  
--  exploited as simple reachability via given dels.
actsForB :: DelClosure ->
            (CoreBase, CoreBase) ->
            Maybe ActsForProof
actsForB delClosure (p,q) 
  | p == top = Just AFTop
  | q == bot = Just AFBot
  | p == q  = Just AFRefl
  | otherwise = 
    case find (== p) (superiors q) of
      Just del -> Just $ AFDel (p,q)
      _ -> Nothing
  where
    top :: CoreBase
    top = T
    bot :: CoreBase
    bot = B  
    superiors :: CoreBase -> [CoreBase]
    superiors q = case find ((== q) . fst) delClosure of
                    Just (q, sups) -> sups

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
