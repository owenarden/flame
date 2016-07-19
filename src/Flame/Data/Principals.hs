{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

module Flame.Data.Principals
where

-- External
import Data.Data
import Control.Arrow       ((***))
import Data.Maybe          (mapMaybe)
import Data.Graph 
import Data.List
import Data.Either
import Data.Data

{- The principal data type -}
data Prin =
  Top
  | Bot
  | Name String
  | Conj  Prin Prin 
  | Disj  Prin Prin
  | Conf  Prin
  | Integ Prin
--  | Voice Prin
  deriving (Read, Eq, Show, Data, Typeable)

data ActsForProof =                    
      AFTop
    | AFBot
    | AFRefl 
    | AFDel (Prin, Prin) -- NB: this implicitly uses transitivity on given dels
    | AFConj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFDisj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
  deriving (Read, Eq, Show, Data, Typeable)

join p q  = (Conj (Conj (Conf p) (Conf q)) (Disj (Integ p) (Integ q)))
meet p q  = (Conj (Disj (Conf p) (Conf q)) (Conj (Integ p) (Integ q)))

data Base =
  P String -- ^ Primitive principal
  | B   -- ^ Bottom
  | T   -- ^ Top
  deriving (Eq, Show, Ord)

newtype MNorm = M { unM :: [Base]}
  deriving (Eq, Ord, Show)

newtype JNorm = J { unJ :: [MNorm]}
  deriving (Eq, Ord, Show)

data Norm = N {conf :: JNorm, integ :: JNorm}
  deriving (Eq, Ord, Show)

fromBase :: Base -> Prin
fromBase B = Bot
fromBase T = Top
fromBase (P s) = Name s

type DelClosure = [(JNorm, [JNorm])]

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
    confActsFor = actsForJ True confClosure 
    integActsFor :: (JNorm, JNorm) -> Maybe ActsForProof
    integActsFor = actsForJ False integClosure

actsForJ :: Bool ->
            DelClosure ->
            (JNorm, JNorm) ->
            Maybe ActsForProof
actsForJ isConf delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = --pprTrace "actsForJ" (ppr (p,q)) $
                case conjProofs of
                  Just [conj] -> Just conj
                  _      -> AFConj <$> conjProofs 
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
                                                  actsForM isConf delClosure (pm,qm))
                                                pms
                                  of
                                    (pf:pfs) ->
                                      --pprTrace "found proof" (ppr pf) $
                                      Just pf
                                    [] -> Nothing
                                )
                                qms

actsForM :: Bool ->
            DelClosure ->
            (MNorm, MNorm) ->
            Maybe ActsForProof
actsForM isConf delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = case disjProofs of
                  Just [disj] -> Just disj
                  _      -> AFDisj <$> disjProofs 
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
                                                  actsForB isConf delClosure (pb,qb))
                                                qbs
                                  of
                                    (pf:pfs) -> Just pf
                                    [] -> Nothing
                                )
                                pbs

-- IDEA for transitivity.  If all given dels are expressed "primitively",
-- then transitivity can be exploited as simple reachability via given dels.
actsForB :: Bool ->
            DelClosure ->
            (Base, Base) ->
            Maybe ActsForProof
actsForB isConf delClosure (p,q) 
  | p == top = Just AFTop
  | q == bot = Just AFBot
  | p == q  = Just AFRefl
  | otherwise = --pprTrace "actsForB" (ppr (p,q)) $
    case find (== J [M [p]]) (superiors $ J [M [q]]) of
      Just del -> if isConf then
                     Just $ AFDel (Conf (fromBase p), Conf (fromBase q))
                  else
                     Just $ AFDel (Integ (fromBase p), Integ (fromBase q))
      _ -> Nothing
  where
    top :: Base
    top = T
    bot :: Base
    bot = B  
    superiors :: JNorm -> [JNorm]
    superiors q = case find ((== q) . fst) delClosure of
                    Just (q, sups) -> sups
                    _ -> []

subsequencesOfSize :: Int -> [a] -> [[a]]
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

cartProd :: JNorm -> [JNorm]
cartProd (J ms) = [J $ map mkM ps | ps <- sequence [bs | (M bs) <- ms]]
  where mkM p = M [p]

{-
    - expand given constraints to "base form": conf or integ, no RHS conj, no LHS disj
    - for each conjunction on the LHS, add a pseudo-node to the graph that is
        reachable from each conjunct and from which the intersection of the
        superiors of each conjunct are reachable.
    - for each disjunction on the RHS, add a pseudo-node to the graph that
        reaches the disjunction and is reachable from the intersection of
        the inferiors of each disjunct.
    - fixpoint?
-}
expandGivens :: [(Prin,Prin)]
             -> ([(JNorm,JNorm)], [(JNorm,JNorm)])
expandGivens givens = foldl
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
                      ([] :: [(JNorm, JNorm)], [] :: [(JNorm, JNorm)])
                      [(normPrin p, normPrin q) | (p, q) <- givens]
  
givenClosure :: [(JNorm,JNorm)] -> [(JNorm, [JNorm])]
givenClosure givens =

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

    structJoinEdges :: JNorm -> [(JNorm, JNorm, [JNorm])]
    structJoinEdges (J []) = [] 
    structJoinEdges (J seq) = 
      [(J inf, J inf, [J seq]) | inf <- subsequencesOfSize (length seq - 1) seq]
      ++ concat [structJoinEdges (J inf) | inf <- subsequencesOfSize (length seq - 1) seq]


    structMeetEdges :: JNorm -> [(JNorm, JNorm, [JNorm])]
    structMeetEdges (J [M []]) = [] 
    structMeetEdges (J [M seq]) = 
      [(baseSeqToJ seq, baseSeqToJ seq, map baseSeqToJ $ subsequencesOfSize (length seq - 1) seq)]
      ++ concat [structMeetEdges (J [M sup]) | sup <- subsequencesOfSize (length seq - 1) seq]

    initialEdges :: [(JNorm, JNorm, [JNorm])]
    initialEdges = [(inf, inf, union (union (nub [gsup | (gsup, ginf) <- givens, ginf == inf])
                                            $ concat [jsups | (jinf, _, jsups) <- structJoinEdges inf, jinf == inf])
                                     $ concat [msups | (minf, _, msups) <- structJoinEdges inf, minf == inf])
                    | inf <- principals]

    principals :: [JNorm]
    principals = [top, bot] ++ (nub $ concat [(map J $ concat [subsequencesOfSize i psC | i <- [1..length psC]]) ++
                                              (map baseSeqToJ $ concat [subsequencesOfSize i qs | i <- [1..length qs]])
                                             | (J psC, J [M qs]) <- givens])

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
