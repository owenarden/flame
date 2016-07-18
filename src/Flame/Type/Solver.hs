{-# LANGUAGE CPP             #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Flame.Type.Solver
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
import Data.Either (partitionEithers)
import Data.List   (sort)
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

data Base v s
  = P s -- ^ Primitive principal
  | V v -- ^ Type var
  | B   -- ^ Bottom
  | T   -- ^ Top
  | ConfVoice v -- ^ Voice of type var
  deriving (Eq,Ord)

newtype MNorm v s = M { unM :: [Base v s]}
  deriving (Eq)

instance (Ord v, Ord c) => Ord (MNorm v c) where
  compare (M [x])   (M [y])   = compare x y
  compare (M [_])   (M (_:_)) = LT
  compare (M (_:_)) (M [_])   = GT
  compare (M xs)    (M ys)    = compare xs ys

newtype JNorm v s = J { unJ :: [MNorm v s]}
  deriving (Ord)

instance (Eq v, Eq s) => Eq (JNorm v s) where
  (J []) == (J [M [B]]) = True
  (J [M [B]]) == (J []) = True
  (J ms1) == (J ms2) = ms1 == ms2

data Norm v s = N {conf :: JNorm v s, integ :: JNorm v s}
  deriving (Ord)

instance (Eq v, Eq s) => Eq (Norm v s) where
  N c1 i1 == N c2 i2 = c1 == c2 && i1 == i2

instance (Outputable v, Outputable s)  => Outputable (Norm v s) where
  ppr (N c i) = case (pprSimple c, pprSimple i) of
                  (cS, iS) -> cS <+> text "→ ∧ " <+> iS <+> text "←"
    where
      pprSimple (J [M [P s]]) = ppr s
      pprSimple (J [M [V v]]) = ppr v
      pprSimple (J [M [B]]) = text "⊥"
      pprSimple (J [M [T]]) = text "⊤"
      pprSimple sop           = text "(" <+> ppr sop <+> text ")"

instance (Outputable v, Outputable s) => Outputable (JNorm v s) where
  ppr = hcat . punctuate (text " ∧ ") . map ppr . unJ

instance (Outputable v, Outputable s) => Outputable (MNorm v s) where
  ppr s = text "(" <+> (hcat . punctuate (text " ∨ ") . map ppr . unM) s <+> text ")"

instance (Outputable v, Outputable s) => Outputable (Base v s) where
    ppr (P s)   = ppr s
    ppr (V s)   = ppr s
    ppr B = text "⊥"
    ppr T = text "⊤"
    ppr (ConfVoice v) = text "∇(" <+> ppr v <+> text "→)"

mergeWith :: (a -> a -> Either a a) -> [a] -> [a]
mergeWith _ []      = []
mergeWith op (f:fs) = case partitionEithers $ map (`op` f) fs of
                        ([],_)              -> f : mergeWith op fs
                        (updated,untouched) -> mergeWith op (updated ++ untouched)

-- | Merge two symbols of a Meet term
--
-- Performs the following rewrites:
--
-- @
-- ⊤ ∨ x    ==>  x
-- x ∨ ⊤    ==>  x
-- x ∨ ⊥    ==>  0
-- ⊥ ∨ x    ==>  0
-- x ∨ x    ==>  x
-- @
mergeB :: (Eq v, Eq c) => Base v c -> Base v c
       -> Either (Base v c) (Base v c)
mergeB T r = Left r       -- ⊤ ∨ x ==> x
mergeB l T = Left l       -- x ∨ ⊤ ==> x
mergeB B _ = Left B       -- ⊥ ∨ x ==> ⊥
mergeB _ B = Left B       -- x ∨ ⊥ ==> ⊥
mergeB l r                -- y ∨ y ==> y
  | l == r = Left l
mergeB l _ = Right l

-- | Merge two components of a Join term
--
-- Performs the following rewrites:
--
-- @
-- ⊤ ∧ x       ==>  ⊤ 
-- x ∧ ⊤       ==>  ⊤
-- ⊥ ∧ x       ==>  x
-- x ∧ ⊥       ==>  x
-- x ∧ (x ∨ y) ==>  x  (Absorbtion)
-- (x ∨ y) ∧ x ==>  x  (Absorbtion)
-- @
mergeM :: (Eq v, Eq c) => MNorm v c -> MNorm v c
       -> Either (MNorm v c) (MNorm v c)
mergeM (M [T]) _ = Left (M [T])                   -- ⊤ ∧ x       ==>  ⊤ 
mergeM _ (M [T]) = Left (M [T])                   -- x ∧ ⊤       ==>  ⊤ 
mergeM (M (B:_)) r = Left r                       -- ⊥ ∧ x       ==>  x 
mergeM l (M (B:_)) = Left l                       -- x ∧ ⊥       ==>  x
mergeM (M [l]) (M rs) | elem l rs = Left (M [l])  -- x ∧ (x ∨ y) ==>  x
mergeM (M ls) (M [r]) | elem r ls = Left (M [r])  -- (x ∨ y) ∧ x  ==>  x
mergeM l r | l == r = Left l                      -- y ∧ y    ==>  y
mergeM l _ = Right l

zeroM :: MNorm v c -> Bool
zeroM (M (B:_)) = True
zeroM _         = False

mkNonEmpty :: JNorm v c -> JNorm v c
mkNonEmpty (J []) = J [M [B]]
mkNonEmpty s      = s

-- | Simplifies SOP terms using
--
-- * 'mergeM'
-- * 'mergeB'
simplifyJNorm :: (Ord v, Ord c) => JNorm v c -> JNorm v c
simplifyJNorm = repeatF go
  where
    go = mkNonEmpty
       . J
       . sort . filter (not . zeroM)
       . mergeWith mergeM
       . map (M . sort . mergeWith mergeB . unM)
       . unJ

    repeatF f x =
      let x' = f x
      in  if x' == x
             then x
             else repeatF f x'
{-# INLINEABLE simplifyJNorm #-}

-- | Merge two JNorm terms by join
mergeJNormJoin :: (Ord v, Ord c) => JNorm v c -> JNorm v c -> JNorm v c
mergeJNormJoin (J ms1) (J ms2) = simplifyJNorm $ J (ms1 ++ ms2)
{-# INLINEABLE mergeJNormJoin #-}

-- | Merge two JNorm terms by meet
mergeJNormMeet :: (Ord v, Ord c) => JNorm v c -> JNorm v c -> JNorm v c
mergeJNormMeet (J ms1) (J ms2)
  = simplifyJNorm
  . J
  $ concatMap (zipWith (\p1 p2 -> M (unM p1 ++ unM p2)) ms1 . repeat) ms2
{-# INLINEABLE mergeJNormMeet #-}

-- | Merge two Norm terms by join
mergeNormJoin :: (Ord v, Ord c) => Norm v c -> Norm v c -> Norm v c
mergeNormJoin (N c1 i1) (N c2 i2) = N (mergeJNormJoin c1 c2) (mergeJNormJoin i1 i2)
{-# INLINEABLE mergeNormJoin #-}

-- | Merge two Norm terms by meet
mergeNormMeet :: (Ord v, Ord c) => Norm v c -> Norm v c -> Norm v c
mergeNormMeet (N c1 i1) (N c2 i2) = N (mergeJNormMeet c1 c2) (mergeJNormMeet i1 i2)
{-# INLINEABLE mergeNormMeet #-}

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
                       kvoice        :: TyCon,
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
    kvoiceDataNm <- lookupName md (mkDataOcc "KVoice")
    actsforNm    <- lookupName md (mkTcOcc "≽")
    ktopTc   <- promoteDataCon <$> tcLookupDataCon ktopDataNm
    kbotTc   <- promoteDataCon <$> tcLookupDataCon kbotDataNm
    knameTc  <- promoteDataCon <$> tcLookupDataCon knameDataNm
    kconjTc  <- promoteDataCon <$> tcLookupDataCon kconjDataNm
    kdisjTc  <- promoteDataCon <$> tcLookupDataCon kdisjDataNm
    kconfTc  <- promoteDataCon <$> tcLookupDataCon kconfDataNm
    kintegTc <- promoteDataCon <$> tcLookupDataCon kintegDataNm
    kvoiceTc <- promoteDataCon <$> tcLookupDataCon kvoiceDataNm
    actsforTc  <-  tcLookupTyCon actsforNm
    return FlameRec{
       ktop       = ktopTc
    ,  kbot       = kbotTc
    ,  kname      = knameTc
    ,  kconj      = kconjTc
    ,  kdisj      = kdisjTc
    ,  kconf      = kconfTc
    ,  kinteg     = kintegTc
    ,  kvoice      = kvoiceTc
    ,  actsfor    = actsforTc
    ,  confClosure = []
    ,  integClosure = []
    }
  where
    flameModule  = mkModuleName "Flame.Type.Principals"
    flamePackage = fsLit "flame"

-- | 'Norm' with 'TyVar' variables
type CoreNorm   = Norm TyVar Type
type CoreJNorm  = JNorm TyVar Type
type CoreMNorm  = MNorm TyVar Type
type CoreBase   = Base TyVar Type

-- | Convert a type of /kind/ 'Flame.Principals.KPrin' to a 'JNorm' term
-- flrec contains the KPrin type constructors
-- isConf indicates whether we are normalizing the conf component
jnormPrin :: FlameRec -> Bool -> Type -> CoreJNorm
jnormPrin flrec isConf ty | Just ty1 <- coreView ty = jnormPrin' ty1
  where jnormPrin' = jnormPrin flrec isConf
jnormPrin flrec isConf (TyVarTy v) = J [M [V v]]
jnormPrin flrec isConf (TyConApp tc [])
  | tc == (ktop flrec) = J [M [T]]
  | tc == (kbot flrec) = J [M [B]]
jnormPrin flrec isConf (TyConApp tc [x])
  | tc == (kname flrec) = J [M [P x]]
  | tc == (kconf flrec) =
    if isConf then jnormPrin' x else J [M [B]]
  | tc == (kinteg flrec) = 
    if isConf then J [M [B]] else jnormPrin' x
  | tc == (kvoice flrec) =
    if isConf then J [M [B]] else integ $ voiceOf (normPrin flrec x)
  where jnormPrin' = jnormPrin flrec isConf
jnormPrin flrec isConf (TyConApp tc [x,y])
  | tc == (kconj flrec) = mergeJNormJoin (jnormPrin' x) (jnormPrin' y)
  | tc == (kdisj flrec) = mergeJNormMeet (jnormPrin' x) (jnormPrin' y)
  where jnormPrin' = jnormPrin flrec isConf

-- | Convert a type of /kind/ 'Flame.Principals.KPrin' to a 'JNorm' term
normPrin :: FlameRec -> Type -> CoreNorm
normPrin flrec ty
  | Just ty1 <- coreView ty =
      N (jnormPrin flrec True ty1) (jnormPrin flrec False ty1)
normPrin flrec (TyVarTy v) = N (J [M [V v]]) (J [M [V v]])
normPrin flrec (TyConApp tc [])
  | tc == (ktop flrec) = N (J [M [T]]) (J [M [T]])
  | tc == (kbot flrec) = N (J [M [B]]) (J [M [B]])
normPrin flrec (TyConApp tc [x])
  | tc == (kname flrec) =  N (J [M [P x]]) (J [M [P x]])
  | tc == (kconf flrec) =  N (jnormPrin flrec True x) (J [M [B]])
  | tc == (kinteg flrec) = N (J [M [B]]) (jnormPrin flrec False x)
  | tc == (kvoice flrec) =  voiceOf (normPrin flrec x)
normPrin flrec (TyConApp tc [x,y])
  | tc == (kconj flrec) = let x' = normPrin flrec x in
                          let y' = normPrin flrec y in
                             mergeNormJoin x' y'
  | tc == (kdisj flrec) = let x' = normPrin flrec x in
                          let y' = normPrin flrec y in
                             mergeNormMeet x' y'

voiceOf :: CoreNorm -> CoreNorm
voiceOf (N conf integ) = N (J [M [B]]) (mergeJNormJoin (wrapVars conf) integ)
  where
    wrapVars (J ms) = J (map wrapVars' ms)
    wrapVars' (M bs) = M (map wrapVars'' bs)
    wrapVars'' (V v) = ConfVoice v 
    wrapVars'' (ConfVoice v) = ConfVoice v 
    wrapVars'' p = p
  
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
decideActsFor flrec given derived wanteds = return $! case failed of
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

    flrec' = flrec{confClosure = confClosure,
                   integClosure = --pprTrace "integ closure" (ppr integClosure)
                                  integClosure}

    solved, failed :: [Ct]
    (solved,failed) = (map fst *** map fst)
                      $ partition (\a ->
                                    case actsFor flrec' (snd a) of
                                    Just pf -> --pprTrace "proof" (ppr pf)
                                               True
                                    _       -> --pprTrace "failed" (ppr (snd a))
                                               False
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
                              ((supC, infC), (supI, infI))
                            _ -> pprTrace "not in base form" (ppr given) undefined)
                        givens
  -- TODO: expand given constraints to "base form": conf or integ, no RHS conj, no LHS disj
  {- TODO:
    - for each conjunction on the LHS, add a pseudo-node to the graph that is
        reachable from each conjunct and from which the intersection of the
        superiors of each conjunct are reachable.
    - for each disjunction on the RHS, add a pseudo-node to the graph that
        reaches the disjunction and is reachable from the intersection of
        the inferiors of each disjunct.
    - fixpoint?
  -}

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
  | otherwise = --pprTrace "actsFor" (ppr (p,q)) $
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
  | otherwise = --pprTrace "actsForJ" (ppr (p,q)) $
                AFConj <$> conjProofs 
  where
    top :: CoreJNorm
    top = J [M [T]]
    bot :: CoreJNorm
    bot = J [M [B]] 
    -- for every join comp on rhs, find sup on lhs
    (J pms, J qms) = (p,q)
    conjProofs :: Maybe [ActsForProof]
    conjProofs = sequence $ map (\qm ->
                                  case mapMaybe (\pm ->
                                                  actsForM delClosure (pm,qm))
                                                pms
                                  of
                                    (pf:pfs) ->
                                      --pprTrace "found proof" (ppr pf) $
                                      Just pf
                                    [] -> Nothing
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
                                  case mapMaybe (\qb ->
                                                  actsForB delClosure (pb,qb))
                                                qbs
                                  of
                                    (pf:pfs) -> Just pf
                                    [] -> Nothing
                                )
                                pbs
-- IDEA for transitivity.  If all given dels are expressed "primitively",
-- then transitivity can be exploited as simple reachability via given dels.
actsForB :: DelClosure ->
            (CoreBase, CoreBase) ->
            Maybe ActsForProof
actsForB delClosure (p,q) 
  | p == top = Just AFTop
  | q == bot = Just AFBot
  | p == q  = Just AFRefl
  | otherwise = --pprTrace "actsForB" (ppr (p,q)) $
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
                    _ -> []

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

