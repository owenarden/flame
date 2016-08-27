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

{- A restricted, indexed monad for for flow-limited authorization -}
class Labeled n => FLA (m :: KPrin -> * -> *) (n :: KPrin -> * -> *) where
  lift   :: n l a -> m pc (n l a)
  apply  :: (pc ⊑ pc') => m pc (n l a) -> (n l a -> m pc' (n l' b)) -> m pc' (n l' b)
  lbind  :: (l ⊑ l', l ⊑ pc) => n l a -> (a -> m pc (n l' b)) -> m pc' (n l' b)

  protect :: a -> m pc (n l a)
  protect = lift . label

  assume :: (pc ≽ ((I q) ∧ (∇) q), (∇) p ≽ (∇) q) =>
              (p :≽ q) -> ((p ≽ q) => m pc (n l a)) -> m pc (n l a)
  assume = unsafeAssume
  
  reprotect :: (l ⊑ l', pc ⊑ pc') => m pc (n l a) -> m pc' (n l' a) 
  reprotect x = apply x $ \x' -> lbind x' (protect :: a -> m SU (n l' a))

  use :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => m pc (n l a) -> (a -> m pc' (n l' b)) -> m pc' (n l' b)
  use x f = apply x $ \x' -> lbind x' f

  (*>>=) :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => m pc (n l a) -> (a -> m pc' (n l' b)) -> m pc' (n l' b)
  (*>>=) = use

  lfmap :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => (a -> b) -> m pc (n l a) -> m pc' (n l' b)
  lfmap f x = x *>>= (\y -> protect (f y))

  ljoin  :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => m pc (n l (m pc' (n l' a))) -> m pc' (n l' a)
  ljoin x = x *>>= id

 
  {- XXX: The below operations will become unecessary with a GLB solver -}
  liftx :: SPrin pc -> n l a -> m pc (n l a)
  liftx pc = lift

  protectx :: SPrin pc ->  a -> m pc (n l a)
  protectx pc = protect

  reprotectx :: (l ⊑ l', pc ⊑ pc') => SPrin pc' -> SPrin l' -> m pc (n l a) -> m pc' (n l' a) 
  reprotectx  pc' l' x = apply x $ \x' -> lbind x' (protect :: a -> m SU (n l' a))

infixl 4 **>

--instance Labeled n => RLFunctor n where
--  type MayUse n (l :: KPrin) a (l' :: KPrin) b = l ⊑ l'
--  fmap f action = bind action $ \a -> label $ f a 
--
--instance Labeled n => RLApplicative n where
--  pure = label
--  a <*> b  = bind a $ \f ->
--              bind b $ \b' -> label $ f b'
--
--instance Labeled n => RLMonad n where
--  return = label
--  (>>=)  = bind

--instance FLA m n => RLFunctor m where
--  type Suitable m (n l a) = Labeled n
--  type MayUse m pc (n l a) pc' (n l' b) = (pc ⊑ pc')
--  fmap :: (pc ⊑ pc') => (n l a -> n l' b) -> m pc (n l a) -> m pc' (n l' b)
--  fmap f action = apply action $ \a -> lift $ f a

--
--instance Labeled n => RLApplicative n where
--  pure = label
--  a <*> b  = bind a $ \f ->
--              bind b $ \b' -> label $ f b'
--
--instance Labeled n => RLMonad n where
--  return = label
--  (>>=)  = bind

--instance FLA m n => RIFunctor m where

  

--instance FLA m n => RIFunctor m where
--  type Suitable m (pc,l) (n l a) = Labeled n
--  fmap f action = lfmap

--data instance Constraints (CtlT e pc) (n l a) = Labeled n => IsLabeled
--instance Labeled n => Suitable (CtlT e pc) (n l a) where
--   constraints = IsLabeled

--
--instance Labeled n => RIApplicative n where
--  type (≤*) (x :: KPrin) (y :: KPrin) = x ⊑ y
--  pure = label
--  a <*> b  = bind a $ \f ->
--              bind b $ \b' -> label $ f b'
--
--instance Labeled n => RIMonad n where
--  return = label
--  (>>=)  = bind

{- A restricted, indexed monad for for flow-limited authorization -}
  

{- A type for pure labeled computations -}
data Lbl (l::KPrin) a where
  UnsafeMkLbl :: { unsafeRunLbl :: a } -> Lbl l a
-- both the constructor and destructor must be private:
--   since either will unlabel a value
--   (the constructor enables pattern matching)

instance Labeled Lbl where
  label = lbl_label
  bind = lbl_bind
  unlabelPT = lbl_unlabelPT 
  unlabelU = lbl_unlabelU

instance Labeled n => Functor (n l) where
  fmap f action = bind action $ \a -> label $ f a 

instance Labeled n => Applicative (n l) where
  pure = label
  a <*> b  = bind a $ \f ->
              bind b $ \b' -> label $ f b'

instance Labeled n => Monad (n l) where
  return = label
  (>>=) = bind

lbl_label :: a -> Lbl l a
lbl_label = UnsafeMkLbl

lbl_bind :: (l ⊑ l') => Lbl l a -> (a -> Lbl l' b) -> Lbl l' b    
lbl_bind x f = f (unsafeRunLbl x)

lbl_unlabelPT :: Lbl PT a -> a
lbl_unlabelPT a = unsafeRunLbl a

lbl_unlabelU :: Lbl l () -> ()
lbl_unlabelU a = unsafeRunLbl a

{- A transformer for effectful labeled computations -}
data CtlT e (pc::KPrin) a where
  UnsafeIFC :: Monad e => { runIFC :: e a } -> CtlT e pc a

type IFC e pc l a = CtlT e pc (Lbl l a)

ifc_lift :: Monad e => Lbl l a -> IFC e pc l a
ifc_lift  x = UnsafeIFC $ Prelude.return x

ifc_lbind :: (Monad e, l ⊑ l', l ⊑ pc) => Lbl l a -> (a -> IFC e pc l' b) -> IFC e pc' l' b
ifc_lbind x f = UnsafeIFC $ runIFC $ f $ unsafeRunLbl x

ifc_apply :: (Monad e, pc ⊑ pc') => IFC e pc l a -> (Lbl l a -> IFC e pc' l' b) -> IFC e pc' l' b
ifc_apply x f = UnsafeIFC $ do a <- runIFC x
                               runIFC $ f a

--ifc_assume :: (Monad e, pc ≽ (I q ∧ (∇) q), (∇) p ≽ (∇) q) =>
--            (p :≽ q) -> ((p ≽ q) => IFC e pc l a) -> IFC e pc l a
--ifc_assume pf m = 

instance Monad e => FLA (CtlT e) Lbl where
  lift    = ifc_lift 
  lbind   = ifc_lbind
  apply   = ifc_apply
--  assume  = ifc_assume

{- XXX: The below operations will become unecessary with a GLB solver -}
runIFCx :: Monad e => SPrin pc -> CtlT e pc a -> e a
runIFCx pc ctl = runIFC ctl 

runIFCxx :: Monad e => SPrin pc -> SPrin l -> CtlT e pc (Lbl l a) -> e (Lbl l a)
runIFCxx pc l ctl = runIFC ctl 
