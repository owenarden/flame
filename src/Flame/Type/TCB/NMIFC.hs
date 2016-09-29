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
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.Type.TCB.NMIFC
  where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Flame.Type.Principals
import Flame.Type.TCB.Assume
import Flame.Type.TCB.IFC (Labeled(..), Lbl(..))

class Labeled n => NMFLA (m :: (KPrin -> * -> *) -> KPrin -> KPrin -> KPrin -> * -> *) n where
  lift :: n l a -> m n β pc l a

  apply  :: (pc ⊑ pc', β' ⊑ β) => m n β pc l a -> (n l a -> m n β' pc' l' b) -> m n β' pc' l' b

  ebind  :: (l ⊑ l', l ⊑ pc, l ⊑ β) => n l a -> (a -> m n β pc l' b) -> m n β' pc' l' b

  use :: (l ⊑ l', (pc ⊔ l) ⊑ pc', l ⊑ β', β' ⊑ β) => m n β pc l a -> (a -> m n β' pc' l' b) -> m n β' pc' l' b
  use x f = apply x $ \x' -> ebind x' f

  protect :: a -> m n β pc l a
  protect = lift . label
  
  iassume :: (pc ⊑ ((I q) ∧ Δ p), Δ p ⊑ β) =>
              (I p :≽ I q) -> ((I p ≽ I q) => m n β pc l a) -> m n β pc l a
  iassume = unsafeAssume

  cassume :: (pc ≽ (∇) q, (∇) p ≽ (∇) q, (∇) q ⊑ β) =>
              (C p :≽ C q) -> ((C p ≽ C q) => m n β pc l a) -> m n β pc l a
  cassume = unsafeAssume

  reprotect :: (l ⊑ l', pc ⊑ pc', β' ⊑ β) => m n β pc l a -> m n β' pc' l' a 
  reprotect x = apply x $ \x' -> ebind x' (protect :: a -> m n SU SU l' a)

  ffmap :: (l ⊑ l', (pc ⊔ l) ⊑ pc', (pc ⊔ l) ⊑ β', β' ⊑ β) => (a -> b) -> m n β pc l a -> m n β' pc' l' b
  ffmap f x = use x (\y -> protect (f y))

  fjoin  :: (l ⊑ l', (pc ⊔ l) ⊑ pc', (pc ⊔ l) ⊑ β', β' ⊑ β) => m n β pc l (m n β' pc' l' a) -> m n β' pc' l' a
  fjoin x = use x id
  
  {- XXX: The below operations will become unecessary with a GLB solver -}
  liftx :: SPrin pc -> n l a -> m n β pc l a
  liftx pc = lift
  
  protectx :: SPrin pc ->  a -> m n β pc l a
  protectx pc = protect
  
  reprotectx :: (l ⊑ l', pc ⊑ pc', β' ⊑ β) => SPrin pc' -> SPrin l' -> m n β pc l a -> m n β' pc' l' a
  reprotectx pc' l' = reprotect

{- A transformer for effectful labeled computations -}
data NMCtlT e (n :: KPrin -> * -> *) (β :: KPrin) (pc :: KPrin) (l :: KPrin) a where
  UnsafeNMIFC :: Monad e => { runNMIFC :: e (n l a) } -> NMCtlT e n β pc l a

type NMIFC e β pc l a = NMCtlT e Lbl β pc l a

nmifc_lift :: Monad e => Lbl l a -> NMIFC e β pc l a
nmifc_lift  x = UnsafeNMIFC $ Prelude.return x

nmifc_ebind :: (Monad e, l ⊑ l', l ⊑ pc, l ⊑ β) => Lbl l a -> (a -> NMIFC e β pc l' b) -> NMIFC e β' pc' l' b
nmifc_ebind x f = UnsafeNMIFC $ runNMIFC $ f $ unsafeRunLbl x

nmifc_apply :: (Monad e, pc ⊑ pc', β' ⊑ β) => NMIFC e β pc l a -> (Lbl l a -> NMIFC e β' pc' l' b) -> NMIFC e β' pc' l' b
nmifc_apply x f = UnsafeNMIFC $ do a <- runNMIFC x
                                   runNMIFC $ f a

instance Monad e => NMFLA (NMCtlT e) Lbl where
  lift    = nmifc_lift 
  ebind   = nmifc_ebind
  apply   = nmifc_apply

{-
{- XXX: The below operations will become unecessary with a GLB solver -}
runIFCx :: Monad e => SPrin pc -> CtlT e Lbl pc l a -> e (Lbl l a)
runIFCx pc ctl = runIFC ctl 

runIFCxx :: Monad e => SPrin pc -> SPrin l -> CtlT e Lbl pc l a -> e (Lbl l a)
runIFCxx pc l ctl = runIFC ctl 
-}
