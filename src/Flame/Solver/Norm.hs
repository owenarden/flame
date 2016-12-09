{-# LANGUAGE CPP #-}
module Flame.Solver.Norm where

import Flame.Solver.Data  
-- External
import Data.Either   (partitionEithers)
import Data.List     (sort, union, nub)
import Data.Graph    (graphFromEdges, reachable, vertices)
import Data.Function (on)

-- GHC API
import Outputable (Outputable (..), (<+>), text, hcat, punctuate, ppr, pprTrace)
import Type       (cmpType, coreView, mkTyVarTy, mkTyConApp)

#if __GLASGOW_HASKELL__ >= 711
import TyCoRep    (Type (..), TyLit (..))
#else
import TypeRep    (Type (..), TyLit (..))
#endif

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
  | tc == (keye flrec) =
    if isConf then conf $ eyeOf (normPrin flrec x) else J [M [B]]
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
  | tc == (keye flrec) =  eyeOf (normPrin flrec x)
normPrin flrec (TyConApp tc [x,y])
  | tc == (kconj flrec) = let x' = normPrin flrec x in
                          let y' = normPrin flrec y in
                             mergeNormJoin x' y'
  | tc == (kdisj flrec) = let x' = normPrin flrec x in
                          let y' = normPrin flrec y in
                             mergeNormMeet x' y'

voiceOf :: Norm v s -> Norm v s
voiceOf (N conf _) = N (J [M [B]]) (wrapVars conf)
  where
    wrapVars (J ms) = J (map wrapVars' ms)
    wrapVars' (M bs) = M (map wrapVars'' bs)
    wrapVars'' (V v) = VarVoice v 
    wrapVars'' (VarVoice v) = VarVoice v 
    wrapVars'' (VarEye v) = (V v)
    wrapVars'' p = p
  
eyeOf :: Norm v s -> Norm v s
eyeOf (N _ integ) = N (wrapVars integ) (J [M [B]]) 
  where
    wrapVars (J ms) = J (map wrapVars' ms)
    wrapVars' (M bs) = M (map wrapVars'' bs)
    wrapVars'' (V v) = VarEye v 
    wrapVars'' (VarVoice v) = (V v) 
    wrapVars'' (VarEye v) = VarEye v 
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


cartProd :: CoreJNorm -> [CoreJNorm]
cartProd (J ms) = [J $ map mkM ps | ps <- sequence [bs | (M bs) <- ms]]
  where mkM p = M [p]

flattenDelegations :: [(CoreNorm,CoreNorm)]
             -> ([(CoreJNorm,CoreJNorm)], [(CoreJNorm,CoreJNorm)])
flattenDelegations givens = foldl
                      (\(cacc, iacc) given ->
                        case given of
                          -- convert to "base form"
                          -- base form is:
                          --  (b ∧ b ...) ≽ (b ∨ b ...)
                          --   joins of base principals on LHS
                          --   meets of base principals on RHS
                          (N supJC supJI, N (J infMCs) (J infMIs)) -> 
                            ([(supC, J [infC]) | supC <- cartProd supJC, infC <- infMCs] ++ cacc,
                             [(supI, (J [infI])) | supI <- cartProd supJI, infI <- infMIs] ++ iacc)
                      )
                      ([] :: [(CoreJNorm, CoreJNorm)], [] :: [(CoreJNorm, CoreJNorm)])
                      givens
  where
    cartProd (J ms) = [J $ map mkM ps | ps <- sequence [bs | (M bs) <- ms]]
    mkM p = M [p]
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
computeDelClosure :: [(CoreJNorm,CoreJNorm)] -> [(CoreJNorm, [CoreJNorm])]
computeDelClosure givens =
  [(inferior, superiors) | (inferior, _, superiors) <- fixpoint initialEdges]
  where
    top = (J [M [T]])
    bot = (J [M [B]])
    baseSeqToJ seq = J [M seq]
    {-
      For principals in a given in base form, 
        (b ∧ b ...) ≽ (b ∨ b ...)
      we want a node for each subsequence of conjuncts and disjuncts
    -}
    structJoinEdges :: CoreJNorm -> [(CoreJNorm, CoreJNorm, [CoreJNorm])]
    structJoinEdges (J []) = [] 
    structJoinEdges (J seq) = 
      [(J inf, J inf, [J seq]) | inf <- subsequencesOfSize (length seq - 1) seq]
      ++ concat [structJoinEdges (J inf) | inf <- subsequencesOfSize (length seq - 1) seq]

    structMeetEdges :: CoreJNorm -> [(CoreJNorm, CoreJNorm, [CoreJNorm])]
    structMeetEdges (J [M []]) = [] 
    structMeetEdges (J [M seq]) = 
      [(baseSeqToJ seq, baseSeqToJ seq, map baseSeqToJ $ subsequencesOfSize (length seq - 1) seq)]
      ++ concat [structMeetEdges (J [M sup]) | sup <- subsequencesOfSize (length seq - 1) seq]

    initialEdges :: [(CoreJNorm, CoreJNorm, [CoreJNorm])]
    initialEdges = [(inf, inf, union (union (nub [gsup | (gsup, ginf) <- givens, ginf == inf])
                                            $ concat [jsups | (jinf, _, jsups) <- structJoinEdges inf, jinf == inf])
                                     $ concat [msups | (minf, _, msups) <- structJoinEdges inf, minf == inf])
                    | inf <- principals]

    principals :: [CoreJNorm]
    principals = [top, bot] ++ (nub $ concat [(map J $ concat [subsequencesOfSize i psC | i <- [1..length psC]]) ++
                                              (map baseSeqToJ $ concat [subsequencesOfSize i qs | i <- [1..length qs]])
                                             | (J psC, J [M qs]) <- givens])
    -- http://stackoverflow.com/questions/21265454/subsequences-of-length-n-from-list-performance
    subsequencesOfSize :: Int -> [a] -> [[a]]
    subsequencesOfSize n xs = let l = length xs
                              in if n>l then [] else subsequencesBySize xs !! (l-n)
    subsequencesBySize [] = [[[]]]
    subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                              in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

    fixpoint edges = let (graph, vtxToEdges, prinToVtx) = graphFromEdges edges in
                     let vtxToPrin v = let (x, _, _) = vtxToEdges v in x in
                     let newEdges = [(vtxToPrin inf, vtxToPrin inf, 
                                                        (map vtxToPrin $ reachable graph inf) ++
                                                        computeStructEdges (graph, vtxToEdges, prinToVtx) inf)
                                    | inf <- vertices graph] in
                     if edges == newEdges then
                       newEdges 
                     else
                       fixpoint newEdges

    computeStructEdges (graph, vtxToEdges, prinToVtx) vtx = []

