module Flame.Normalize
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
import Flame.Principals

-- External
import Data.Either (partitionEithers)
import Data.List   (sort)
-- GHC API

import Outputable  (Outputable (..), (<+>), text, hcat, integer, punctuate)

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

