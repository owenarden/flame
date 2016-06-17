{-# LANGUAGE DeriveDataTypeable #-}

module Flame.Principals.Dynamic
where
import Data.Data
import Data.Either (partitionEithers)
import Data.List   (partition, sort, find, group)

{- The principal data type -}
data Prin =
  Top
  | Bot
  | Name String
  | Conj  Prin Prin 
  | Disj  Prin Prin
  | Conf  Prin
  | Integ Prin
  | Voice Prin
  deriving (Read, Eq, Show, Data, Typeable)

data Base =
  P String -- ^ Primitive principal
  | B   -- ^ Bottom
  | T   -- ^ Top
  deriving (Eq, Ord, Show, Read, Data, Typeable)

newtype MNorm = M { unM :: [Base]}
  deriving (Eq, Ord, Show, Read, Data, Typeable)

newtype JNorm = J { unJ :: [MNorm]}
  deriving (Eq, Ord, Show, Read, Data, Typeable)

data Norm = N {conf :: JNorm, integ :: JNorm}
  deriving (Eq, Ord, Show, Read, Data, Typeable)

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

data ActsForProof =                    
      AFTop
    | AFBot
    | AFRefl 
    | AFDel (Base, Base) -- NB: this implicitly uses transitivity on given dels
    | AFConj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFDisj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
  deriving (Read, Eq, Show, Data, Typeable)
