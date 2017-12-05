{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Scratch where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection
import Data.Functor.Identity 

import Flame.Principals
import Flame.TCB.Assume

data Label (c :: * -> Constraint) (l::KPrin) a where
  Return :: c a => a -> Label c l a
  Bind   :: (c a, l ⊑ l') => Label c l a -> (a -> Label c l' b) -> Label c l' b

showLabel :: Label c l a -> String
showLabel (Return a) = "(Return " ++ (show a) ++ ")"
showLabel (Bind lv f) = "(Bind " ++ (show lv) ++ (show f) ++ ")"

instance Show a => Show (Label c l a) where
  show = showLabel

lbl_runLabel :: Label c l a -> Label c l a
lbl_runLabel (Return v)   = Return v
lbl_runLabel (Bind lv f) = let (Return v) = lbl_runLabel lv in (f v)


lbl_unsafeUnlabel :: Label c l a  -> a
lbl_unsafeUnlabel (Return v) = v
lbl_unsafeUnlabel (Bind lv f) = let v = lbl_unsafeUnlabel lv in
                                  lbl_unsafeUnlabel (f v)

testAdd :: Lbl l Int -> Lbl l Int -> Int
testAdd a b = unsafeUnlabel $ bind a $ \a' -> 
                              bind b $ \b' -> label (a' + b')

class Labeled (c :: * -> Constraint) (n :: (* -> Constraint) -> KPrin -> * -> *) where
  label         :: c a => a -> n c l a
  bind          :: (c a, c b, l ⊑ l') => n c l a -> (a -> n c l' b) -> n c l' b
  unsafeUnlabel :: c a => n c l a -> a
  relabel       :: (c a, l ⊑ l') => n c l a -> n c l' a
  relabel a = bind a label 

instance Labeled c Label where
  label         = Return
  bind          = Bind
  unsafeUnlabel = lbl_unsafeUnlabel

class CTrue a where {}
instance CTrue a where {}

class IsEDSL a where {}
instance IsEDSL (HighExp a) where {}

type Lbl l a = Label CTrue l a

data FLAC (c :: * -> Constraint) e (n :: (* -> Constraint) -> KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  Lift          :: (c a, Monad e) => n c l a -> FLAC c e n pc l a
  EBind         :: (c a, c b, Monad e, l ⊑ l', l ⊑ pc') => n c l a -> (a -> FLAC c e n pc' l' b) -> FLAC c e n pc l' b
  Apply         :: (c a, c b, Monad e, pc ⊑ pc', pc ⊑ pc'') => FLAC c e n pc l a -> (n c l a -> FLAC c e n pc' l' b) -> FLAC c e n pc'' l' b
  Join          :: (c a, l ⊑ l',  pc ⊑ pc', l ⊑ pc') => FLAC c e n pc l (FLAC c e n pc' l' a) -> FLAC c e n pc' l' a
  UnsafeProtect :: (c a, Monad e) => e (n c l a) -> FLAC c e n pc l a