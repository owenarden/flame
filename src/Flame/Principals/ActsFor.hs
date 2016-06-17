module Flame.Principals.ActsFor
  ( -- * JNorm types
    Base (..)
  , MNorm (..)
  , JNorm (..)
  , Norm (..)
    -- * Simplification
  , mergeB
  , mergeM
  , mergeJNormJoin
  , mergeJNormMeet
  , mergeNormJoin
  , mergeNormMeet
  )
where
import Flame.Principals.Dynamic

-- External
import Control.Arrow       ((***))
import Data.Maybe          (mapMaybe)
import Data.Either (partitionEithers)
import Data.List   (partition, sort, find, group)
import Data.Graph 

data Base =
  P String -- ^ Primitive principal
  | B   -- ^ Bottom
  | T   -- ^ Top
  deriving (Eq, Ord, Show)

newtype MNorm = M { unM :: [Base]}
  deriving (Eq, Ord, Show)

newtype JNorm = J { unJ :: [MNorm]}
  deriving (Eq, Ord, Show)

data Norm = N {conf :: JNorm, integ :: JNorm}
  deriving (Eq, Ord, Show)


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
mergeB :: Base -> Base -> Either Base Base
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
mergeM :: MNorm -> MNorm -> Either MNorm MNorm
mergeM (M [T]) _ = Left (M [T])                   -- ⊤ ∧ x       ==>  ⊤ 
mergeM _ (M [T]) = Left (M [T])                   -- x ∧ ⊤       ==>  ⊤ 
mergeM (M (B:_)) r = Left r                       -- ⊥ ∧ x       ==>  x 
mergeM l (M (B:_)) = Left l                       -- x ∧ ⊥       ==>  x
mergeM (M [l]) (M rs) | elem l rs = Left (M [l])  -- x ∧ (x ∨ y) ==>  x
mergeM (M ls) (M [r]) | elem r ls = Left (M [r])  -- (x ∨ y) ∧ x  ==>  x
mergeM l r | l == r = Left l                      -- y ∧ y    ==>  y
mergeM l _ = Right l

zeroM :: MNorm -> Bool
zeroM (M (B:_)) = True
zeroM _         = False

mkNonEmpty :: JNorm -> JNorm 
mkNonEmpty (J []) = J [M [B]]
mkNonEmpty s      = s

-- | Simplifies SOP terms using
--
-- * 'mergeM'
-- * 'mergeB'
simplifyJNorm :: JNorm -> JNorm 
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
mergeJNormJoin :: JNorm -> JNorm -> JNorm 
mergeJNormJoin (J ms1) (J ms2) = simplifyJNorm $ J (ms1 ++ ms2)
{-# INLINEABLE mergeJNormJoin #-}

-- | Merge two JNorm terms by meet
mergeJNormMeet :: JNorm -> JNorm -> JNorm
mergeJNormMeet (J ms1) (J ms2)
  = simplifyJNorm
  . J
  $ concatMap (zipWith (\p1 p2 -> M (unM p1 ++ unM p2)) ms1 . repeat) ms2
{-# INLINEABLE mergeJNormMeet #-}

-- | Merge two Norm terms by join
mergeNormJoin :: Norm -> Norm -> Norm 
mergeNormJoin (N c1 i1) (N c2 i2) = N (mergeJNormJoin c1 c2) (mergeJNormJoin i1 i2)
{-# INLINEABLE mergeNormJoin #-}

-- | Merge two Norm terms by meet
mergeNormMeet :: Norm -> Norm -> Norm
mergeNormMeet (N c1 i1) (N c2 i2) = N (mergeJNormMeet c1 c2) (mergeJNormMeet i1 i2)
{-# INLINEABLE mergeNormMeet #-}

-- | Convert a 'Prin' to a 'JNorm' term
-- isConf indicates whether we are normalizing the conf component
jnormPrin :: Bool -> Prin -> JNorm
jnormPrin isConf Top = J [M [T]]
jnormPrin isConf Bot = J [M [B]]
jnormPrin isConf (Name s) = J [M [P s]]
jnormPrin isConf (Conf p) = 
  if isConf then jnormPrin isConf p else J [M [B]]
jnormPrin isConf (Integ p) = 
  if isConf then J [M [B]] else jnormPrin isConf p
jnormPrin isConf (Conj p q) =
  mergeJNormJoin (jnormPrin isConf p) (jnormPrin isConf q)
jnormPrin isConf (Disj p q) =
  mergeJNormMeet (jnormPrin isConf p) (jnormPrin isConf q)

-- | Convert a 'Prin' to a 'JNorm' term
normPrin :: Prin-> Norm
normPrin Top        = N (J [M [T]]) (J [M [T]])
normPrin Bot        = N (J [M [B]]) (J [M [B]])
normPrin (Name s)   = N (J [M [P s]]) (J [M [P s]])
normPrin (Conf p)   = N (jnormPrin True p) (J [M [B]]) 
normPrin (Integ p)  = N (J [M [B]]) (jnormPrin False p)
normPrin (Conj p q) = mergeNormJoin (normPrin p) (normPrin q)
normPrin (Disj p q) = mergeNormMeet (normPrin p) (normPrin q)

voiceOf :: Norm -> Norm
voiceOf (N conf integ) = N (J [M [B]]) (mergeJNormJoin conf integ)

type DelClosure = [(Base, [Base])]

data ActsForProof =                    
      AFTop
    | AFBot
    | AFRefl 
    | AFDel (Base, Base) -- NB: this implicitly uses transitivity on given dels
    | AFConj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFDisj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
  deriving (Eq, Show)

actsFor :: DelClosure -- ^ [G]iven conf delegations
           -> DelClosure -- ^ [G]iven integ delegations
           -> (Prin , Prin)
           -> Maybe ActsForProof
actsFor confClosure integClosure (Top, q) = Just AFTop
actsFor confClosure integClosure (p , Bot) = Just AFBot
actsFor confClosure integClosure (p,q)
  | p == q    = Just AFRefl
  | otherwise = --pprTrace "actsFor" (ppr (p,q)) $
        let p' = normPrin p in
        let q' = normPrin q in do
          confPf <- confActsFor (conf p', conf q')
          integPf <- integActsFor (integ p', integ q')
          Just $ AFConj [confPf, integPf]
  where
    top :: Norm
    top = N (J [M [T]]) (J [M [T]])
    bot :: Norm
    bot = N (J [M [B]]) (J [M [B]])

    confActsFor :: (JNorm, JNorm) -> Maybe ActsForProof
    confActsFor = actsForJ confClosure 
    integActsFor :: (JNorm, JNorm) -> Maybe ActsForProof
    integActsFor = actsForJ integClosure

actsForJ :: DelClosure ->
            (JNorm, JNorm) ->
            Maybe ActsForProof
actsForJ delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = --pprTrace "actsForJ" (ppr (p,q)) $
                AFConj <$> conjProofs 
  where
    top :: JNorm
    top = J [M [T]]
    bot :: JNorm
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
            (MNorm, MNorm) ->
            Maybe ActsForProof
actsForM delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = AFDisj <$> disjProofs
  where
    top :: MNorm
    top = M [T]
    bot :: MNorm
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
            (Base, Base) ->
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
    top :: Base
    top = T
    bot :: Base
    bot = B  
    superiors :: Base -> [Base]
    superiors q = case find ((== q) . fst) delClosure of
                    Just (q, sups) -> sups
                    _ -> []

computeDelClosures :: [(Prin,Prin)] -> (DelClosure, DelClosure)
computeDelClosures givens =
  let (confGivens, integGivens) = unzip $ map
                        (\(p,q) ->
                          case (normPrin p, normPrin q) of
                            -- TODO: This fails on givens that aren't already in base form
                            (N (J [M [supC]]) (J [M [supI]]), 
                             N (J [M [infC]]) (J [M [infI]])) -> 
                              ((supC, infC), (supI, infI))
                            _ -> error "not in base form" )
                        givens
  in (computeClosure confGivens,  computeClosure integGivens) 
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

computeClosure :: [(Base,Base)] -> DelClosure
computeClosure givens = 
    map (\q -> (q, case prinToVtx q of
                   Just vtx -> map vtxToPrin $ reachable graph vtx))
        principals
  where
    principals :: [Base]
    principals = [T, B] ++ (map head . group . sort $ (map inferior givens ++ map superior givens))

    edges :: [(Base, Base, [Base])]
    edges =  map (\inf ->
                   (inf, inf, [superior af | af  <- givens, inferior af == inf]))
                 principals
    (graph, vtxToEdges, prinToVtx) = graphFromEdges edges

    vtxToPrin :: Vertex -> Base
    vtxToPrin v = let (x, _, _) = vtxToEdges v in x

    inferior :: (Base,Base) -> Base
    inferior = snd

    superior :: (Base,Base) -> Base
    superior = fst
