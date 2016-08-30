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

module Flame.Type.TCB.IFC
  where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection
--import Control.RLMonad

import Flame.Type.Principals

{-
-------------------------------------------------------------------------------------
  Machinery for dynamically extending the acts-for relation 
  Modified from: https://www.schoolofhaskell.com/user/thoughtpolice/using-reflection
-------------------------------------------------------------------------------------
-}
     
{-
  A type class representing the assumption context.
  Delegations are added to the assumption context via 'using'
-}
class Pi del where

{- Allow proofs to derive from dynamic relationships -}
instance Reifies s (Def Pi a) => Pi (Lift Pi a s) where

data Lift (p :: * -> Constraint) (a :: *) (s :: *) = Lift { lower :: a }

class ReifiableConstraint p where
  data Def (p :: * -> Constraint) (a :: *) :: *
  reifiedIns :: Reifies s (Def p a) :- p (Lift p a s)
 
data AFType (p :: KPrin) (q :: KPrin) = AFType { sup :: SPrin p, inf :: SPrin q}

instance ReifiableConstraint Pi where
  data Def Pi (AFType p q) = Del { sup_ :: SPrin p, inf_ :: SPrin q}
  reifiedIns = Sub Dict

-- Should not be exported
unsafeAssume :: forall a p q. (p :≽ q) -> ((p ≽ q) => a) -> a
unsafeAssume d m = reify d $ \(_ :: Proxy s) ->
  let replaceProof :: Reifies s (Def Pi (AFType p q)) :- (p ≽ q)
      replaceProof = trans proof reifiedIns
        where proof = unsafeCoerceConstraint :: Pi (Lift Pi (AFType p q) s) :- (p ≽ q)
  in m \\ replaceProof

{- Type synonyms for the types of authority evidence terms -}
type (:≽) p q  = Def Pi (AFType p q)
type (:=>=) p q = Def Pi (AFType p q)
type (:⊑) p q  = Def Pi (AFType (C q ∧ I p) (C p ∧ I q))
type (:<:) p q = Def Pi (AFType (C q ∧ I p) (C p ∧ I q))

{- Infix operators for constructing authority evidence terms -}
(≽) :: SPrin p -> SPrin q -> Def Pi (AFType p q)
(≽) p q = Del p q

(=>=) :: SPrin p -> SPrin q -> Def Pi (AFType p q)
(=>=) = (≽)

(⊑) :: SPrin p -> SPrin q -> Def Pi (AFType (C q ∧ I p) (C p ∧ I q))
(⊑) p q = ((q*→) *∧ (p*←)) ≽ ((p*→) *∧ (q*←))

(<:) :: SPrin p -> SPrin q -> Def Pi (AFType (C q ∧ I p) (C p ∧ I q))
(<:) = (⊑)

infix 5 ≽,=>=,⊑,<:

{- An indexed monad for information flow on pure computation -}
class Labeled (n :: KPrin -> * -> *) where
  label     :: a -> n l a
  bind      :: (l ⊑ l') => n l a -> (a -> n l' b) -> n l' b
  unlabelPT :: n PT a -> a
  unlabelU  :: n l () -> ()
  
  relabel :: (l ⊑ l') => n l a -> n l' a
  relabel a = bind a label

{- A monad-like type class for for flow-limited authorization -}
class Labeled n => FLA (m :: (KPrin -> * -> *) -> KPrin -> KPrin -> * -> *) n where
  lift   :: n l a -> m n pc l a

  apply  :: (pc ⊑ pc') => m n pc l a -> (n l a -> m n pc' l' b) -> m n pc' l' b

  ebind  :: (l ⊑ l', l ⊑ pc) => n l a -> (a -> m n pc l' b) -> m n pc' l' b

  protect :: a -> m n pc l a
  protect = lift . label

  use :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => m n pc l a -> (a -> m n pc' l' b) -> m n pc' l' b
  use x f = apply x $ \x' -> ebind x' f

  assume :: (pc ≽ ((I q) ∧ (∇) q), (∇) p ≽ (∇) q) =>
              (p :≽ q) -> ((p ≽ q) => m n pc l a) -> m n pc l a
  assume = unsafeAssume

  reprotect :: (l ⊑ l', pc ⊑ pc') => m n pc l a -> m n pc' l' a 
  reprotect x = apply x $ \x' -> ebind x' (protect :: a -> m n SU l' a)
  ffmap :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => (a -> b) -> m n pc l a -> m n pc' l' b
  ffmap f x = use x (\y -> protect (f y))

  fjoin  :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => m n pc l (m n pc' l' a) -> m n pc' l' a
  fjoin x = use x id
 
  {- XXX: The below operations will become unecessary with a GLB solver -}
  liftx :: SPrin pc -> n l a -> m n pc l a
  liftx pc = lift

  protectx :: SPrin pc ->  a -> m n pc l a
  protectx pc = protect

  reprotectx :: (l ⊑ l', pc ⊑ pc') => SPrin pc' -> SPrin l' -> m n pc l a -> m n pc' l' a
  reprotectx pc' l' x = apply x $ \x' -> ebind x' (protect :: a -> m n SU l' a)


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
  UnsafeIFC :: Monad e => { runIFC :: e (n l a) } -> CtlT e n pc l a

type IFC e pc l a = CtlT e Lbl pc l a

ifc_lift :: Monad e => Lbl l a -> IFC e pc l a
ifc_lift  x = UnsafeIFC $ Prelude.return x

ifc_ebind :: (Monad e, l ⊑ l', l ⊑ pc) => Lbl l a -> (a -> IFC e pc l' b) -> IFC e pc' l' b
ifc_ebind x f = UnsafeIFC $ runIFC $ f $ unsafeRunLbl x

ifc_apply :: (Monad e, pc ⊑ pc') => IFC e pc l a -> (Lbl l a -> IFC e pc' l' b) -> IFC e pc' l' b
ifc_apply x f = UnsafeIFC $ do a <- runIFC x
                               runIFC $ f a

instance Monad e => FLA (CtlT e) Lbl where
  lift    = ifc_lift 
  ebind   = ifc_ebind
  apply   = ifc_apply
--  assume  = ifc_assume

{- XXX: The below operations will become unecessary with a GLB solver -}
runIFCx :: Monad e => SPrin pc -> CtlT e Lbl pc l a -> e (Lbl l a)
runIFCx pc ctl = runIFC ctl 

runIFCxx :: Monad e => SPrin pc -> SPrin l -> CtlT e Lbl pc l a -> e (Lbl l a)
runIFCxx pc l ctl = runIFC ctl 
