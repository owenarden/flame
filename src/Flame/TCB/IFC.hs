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
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.TCB.IFC
  where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Flame.Principals
import Flame.TCB.Assume

{- An indexed monad for information flow on pure computation -}
class Labeled (n :: KPrin -> * -> *) where
  label     :: a -> n l a
  bind      :: (l ⊑ l') => n l a -> (a -> n l' b) -> n l' b
  unlabelPT :: n PT a -> a
  unlabelU  :: n l () -> ()
  unsafeUnlabel :: n l a -> a
  
  relabel :: (l ⊑ l') => n l a -> n l' a
  relabel a = bind a label

{- A monad-like type class for for flow-limited authorization -}
class (Monad e, Labeled n) => FLA (m :: (* -> *) -> (KPrin -> * -> *) -> KPrin -> KPrin -> * -> *) e n where
  lift   :: n l a -> m e n pc l a

  apply  :: (pc ⊑ pc', pc ⊑ pc'') => m e n pc l a -> (n l a -> m e n pc' l' b) -> m e n pc'' l' b

  ebind  :: (l ⊑ l', l ⊑ pc) => n l a -> (a -> m e n pc l' b) -> m e n pc' l' b

  unsafeProtect :: e (n l a) -> m e n pc l a

  runFLA :: m e n pc l a -> e (n l a)

  protect :: a -> m e n pc l a
  protect = lift . label

  use :: forall l l' pc pc' pc'' a b. (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'') =>
         m e n pc l a -> (a -> m e n pc' l' b) -> m e n pc'' l' b
  use x f = apply x $ \x' -> (ebind x' f :: m e n pc' l' b)
 
  assume :: (pc ≽ ((I q) ∧ (∇) q), (∇) p ≽ (∇) q) =>
              (p :≽ q) -> ((p ≽ q) => m e n pc l a) -> m e n pc l a
  assume = unsafeAssume

  reprotect :: forall l l' pc pc' a. (l ⊑ l', pc ⊑ pc') => m e n pc l a -> m e n pc' l' a 
  reprotect x = use x (protect :: a -> m e n SU l' a)

  ffmap :: forall l l' pc pc' a b. (l ⊑ l', pc ⊑ pc', l ⊑ pc') => (a -> b) -> m e n pc l a -> m e n pc' l' b
  ffmap f x = use x (\x' -> protect (f x') :: m e n pc' l' b)

  fjoin  :: forall l l' pc pc' a. (l ⊑ l',  pc ⊑ pc', l ⊑ pc') => m e n pc l (m e n pc' l' a) -> m e n pc' l' a
  fjoin x = use x id

class FLA m e n => BFLA c m e n where
  lift_b :: n l a -> c m e n β pc l a

  apply_b  :: (pc ⊑ pc', pc ⊑ pc'', β' ⊑ β) => c m e n β pc l a -> (n l a -> c m e n β' pc' l' b) -> c m e n β' pc'' l' b

  ebind_b  :: (l ⊑ l', l ⊑ pc, l ⊑ β, β ⊑ β') => n l a -> (a -> c m e n β pc l' b) -> c m e n β' pc' l' b

  use_b :: (l ⊑ l', pc ⊑ pc', pc ⊑ pc'', l ⊑ pc', l ⊑ β', β' ⊑ β) => c m e n β pc l a -> (a -> c m e n β' pc' l' b) -> c m e n β' pc'' l' b
  use_b x f = apply_b x $ \x' -> ebind_b x' f
  
  clearBounds :: c m e n β pc l a -> m e n pc l a

  protect_b :: a -> c m e n β pc l a
  protect_b = lift_b . label

  iassume :: (pc ⊑ ((I q) ∧ Δ p), β ⊑ Δ p) =>
              (I p :≽ I q) -> ((I p ≽ I q) => c m e n β pc l a) -> c m e n β pc l a
  iassume = unsafeAssume

  vassume :: (pc ⊑ ((∇) q ∧ (Δ ((∇) p))), β ⊑ (Δ ((∇) p))) =>
              ((∇) p :≽ (∇) q) -> (((∇) p ≽ (∇) q) => c m e n β pc l a) -> c m e n β pc l a
  vassume = unsafeAssume

  cassume :: (pc ≽ (∇) q, (∇) p ≽ (∇) q, β ≽ ((∇) q)) => 
              (C p :≽ C q) -> ((C p ≽ C q) => c m e n β pc l a) -> c m e n β pc l a
  cassume = unsafeAssume

  eassume :: (pc ≽ (∇) (Δ q), (∇) (Δ p) ≽ (∇) (Δ q), β ≽ ((∇) (Δ p))) => 
              (Δ p :≽ Δ q) -> ((Δ p ≽ Δ q) => c m e n β pc l a) -> c m e n β pc l a
  eassume = unsafeAssume

  reprotect_b :: (l ⊑ l', pc ⊑ pc', l ⊑ b) => c m e n b pc l a -> c m e n b pc' l' a 
  reprotect_b x = apply_b x $ \x' -> ebind_b x' protect_b 

{- A type for pure labeled computations -}
data Lbl (l::KPrin) a where
  UnsafeMkLbl :: { unsafeRunLbl :: a } -> Lbl l a
-- both the constructor and destructor must be private:
--   since either will unlabel a value
--   (the constructor enables pattern matching)

lbl_label :: a -> Lbl l a
lbl_label = UnsafeMkLbl

lbl_bind :: (l ⊑ l') => Lbl l a -> (a -> Lbl l' b) -> Lbl l' b    
lbl_bind x f = f (unsafeRunLbl x)

lbl_unlabelPT :: Lbl PT a -> a
lbl_unlabelPT a = unsafeRunLbl a

lbl_unlabelU :: Lbl l () -> ()
lbl_unlabelU a = unsafeRunLbl a

{- A Labeled instance for Lbl -}
instance Labeled Lbl where
  label = lbl_label
  bind = lbl_bind
  unsafeUnlabel = unsafeRunLbl
  unlabelPT = lbl_unlabelPT 
  unlabelU = lbl_unlabelU

{- A Monad instance of Lbl at a fixed l -}
--instance Labeled n => Functor (n l) where
--  fmap f action = bind action $ \a -> label $ f a 
--
--instance Labeled n => Applicative (n l) where
--  pure = label
--  a <*> b  = bind a $ \f ->
--              bind b $ \b' -> label $ f b'
--
--instance Labeled n => Monad (n l) where
--  return = label
--  (>>=) = bind

{- A transformer for effectful labeled computations -}
data CtlT e (n :: KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  UnsafeIFC :: { runIFC :: e (n l a) } -> CtlT e n pc l a

type IFC e pc l a = CtlT e Lbl pc l a

ifc_lift :: Monad e => Lbl l a -> IFC e pc l a
ifc_lift  x = UnsafeIFC $ Prelude.return x
            
ifc_ebind :: (Monad e, l ⊑ l', l ⊑ pc') => Lbl l a -> (a -> IFC e pc' l' b) -> IFC e pc l' b
ifc_ebind x f = UnsafeIFC $ runIFC $ f $ unsafeRunLbl x

ifc_apply :: (Monad e, pc ⊑ pc', pc ⊑ pc'') => IFC e pc l a -> (Lbl l a -> IFC e pc' l' b) -> IFC e pc'' l' b
ifc_apply x f = UnsafeIFC $ do a <- runIFC x
                               runIFC $ f a

instance Monad e => FLA CtlT e Lbl where
  lift    = ifc_lift 
  ebind   = ifc_ebind
  apply   = ifc_apply
  unsafeProtect = UnsafeIFC
  runFLA  = runIFC

{- A transformer for effectful labeled computations -}
data ClrT m e n (β :: KPrin) (pc :: KPrin) (l :: KPrin) a where
  UnsafeClr :: { runClr :: m e n pc l a } -> ClrT m e n β pc l a

type BIFC e β pc l a = ClrT CtlT e Lbl β pc l a


bfla_lift :: FLA m e n => n l a -> ClrT m e n β pc l a
bfla_lift  x = UnsafeClr $ unsafeProtect $ Prelude.return x

bfla_ebind :: (FLA m e n, l ⊑ l', l ⊑ pc, l ⊑ β, β ⊑ β') => n l a -> (a -> ClrT m e n β pc l' b) -> ClrT m e n β' pc' l' b
bfla_ebind x f = UnsafeClr $ unsafeProtect $ runFLA . runClr $ f $ unsafeUnlabel x

bfla_apply :: (FLA m e n, pc ⊑ pc', pc ⊑ pc'', β' ⊑ β) => ClrT m e n β pc l a -> (n l a -> ClrT m e n β' pc' l' b) -> ClrT m e n β' pc'' l' b
bfla_apply x f = UnsafeClr $ unsafeProtect $ do a <- runFLA $ runClr x
                                                runFLA $ runClr (f a)

instance FLA m e n => BFLA ClrT m e n where
  lift_b      = bfla_lift 
  ebind_b     = bfla_ebind
  apply_b     = bfla_apply
  clearBounds = runClr
