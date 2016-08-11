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
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.Type.TCB.IFC
  where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

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

{- A type synonym for associating a pure and effectful labeled computation type -}
type FLA (m :: KPrin -> * -> *) (n :: KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a = m pc (n l a)
                                                                                               
class FMonad (n :: KPrin -> * -> *) where
  label :: a -> n l a
  bind  :: (l ⊑ l') => n l a -> (a -> n l' b) -> n l' b
  unlabelPT :: n PT a -> a
  unlabelU :: n l () -> ()
  
  relabel :: (l ⊑ l') => n l a -> n l' a
  relabel a = bind a label

{- A monad-like class for flow-limited authorization -}
class FMonad n => FLAMonad (m :: KPrin -> * -> *) (n :: KPrin -> * -> *) where
  lift   :: n l a -> FLA m n pc l a
  apply  :: (pc ⊑ pc') => FLA m n pc l a -> (n l a -> FLA m n pc' l' b) -> FLA m n pc' l' b
  lbind  :: (l ⊑ l', l ⊑ pc) => n l a -> (a -> FLA m n pc l' b) -> FLA m n pc' l' b
  assume :: (pc ≽ ((I q) ∧ (∇) q), (∇) p ≽ (∇) q) =>
              (p :≽ q) -> ((p ≽ q) => FLA m n pc l a) -> FLA m n pc l a

  protect :: a -> FLA m n pc l a
  protect = lift . label
  reprotect :: (l ⊑ l', pc ⊑ pc') => FLA m n pc l a -> FLA m n pc' l' a 
  reprotect x = apply x $ \x' -> lbind x' (protect :: a -> FLA m n SU l' a)

  use :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => FLA m n pc l a -> (a -> FLA m n pc' l' b) -> FLA m n pc' l' b
  use x f = apply x $ \x' -> lbind x' f

  (*>>=) :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => FLA m n pc l a -> (a -> FLA m n pc' l' b) -> FLA m n pc' l' b
  (*>>=) = use

  lfmap :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => (a -> b) -> FLA m n pc l a -> FLA m n pc' l' b
  lfmap f x = x *>>= (\y -> protect (f y))

  ljoin  :: (l ⊑ l', (pc ⊔ l) ⊑ pc') => FLA m n pc l (FLA m n pc' l' a) -> FLA m n pc' l' a
  ljoin x = x *>>= id

  (**>) :: FLA m n pc l a -> FLA m n pc l' b ->  FLA m n pc l' b 
  (**>) a b = apply a $ const b 
 
  {- XXX: The below operations will become unecessary with a GLB solver -}
  liftx :: SPrin pc -> n l a -> FLA m n pc l a
  liftx pc = lift
  protectx :: SPrin pc ->  a -> FLA m n pc l a
  protectx pc = protect
  reprotectx :: (l ⊑ l', pc ⊑ pc') => SPrin pc' -> SPrin l' -> FLA m n pc l a -> FLA m n pc' l' a 
  reprotectx  pc' l' x = apply x $ \x' -> lbind x' (protect :: a -> FLA m n SU l' a)

infixl 4 **>

{- A type for pure labeled computations -}
data Lbl (l::KPrin) a where
  MkLbl :: { unsafeRunLbl :: a } -> Lbl l a

instance Functor (Lbl l) where
  fmap f action = bind action $ \a -> label $ f a 

instance Applicative (Lbl l) where
  pure     = label  
  a <*> b  = bind a $ \f ->
              bind b $ \b' -> label $ f b'

instance Monad (Lbl l) where
  return = lbl_label
  (>>=)  = lbl_bind

instance FMonad Lbl where
  label = lbl_label
  bind = lbl_bind
  unlabelPT = lbl_unlabelPT 
  unlabelU = lbl_unlabelU

lbl_label :: a -> Lbl l a
lbl_label = MkLbl

lbl_bind :: (l ⊑ l') => Lbl l a -> (a -> Lbl l' b) -> Lbl l' b    
lbl_bind x f = f (unsafeRunLbl x)

lbl_unlabelPT :: Lbl PT a -> a
lbl_unlabelPT a = unsafeRunLbl a

lbl_unlabelU :: Lbl l () -> ()
lbl_unlabelU a = unsafeRunLbl a


{- A transformer for effectful labeled computations -}
data CtlT e (pc::KPrin) a where
  UnsafeIFC :: Monad e => { runIFC :: e a } -> CtlT e pc a

runIFCx :: Monad e => SPrin pc -> CtlT e pc a -> e a
runIFCx pc ctl = runIFC ctl 

runIFCxx :: Monad e => SPrin pc -> SPrin l -> CtlT e pc (Lbl l a) -> e (Lbl l a)
runIFCxx pc l ctl = runIFC ctl 
--seq :: (pc ⊑ pc') => IFC e pc l a -> IFC e pc' l' b ->  IFC e pc' l' b 
--seq a b = UnsafeIFC $ do _ <- runIFC a
--                         b <- runIFC b
--                         return $ b

type IFC e pc l a = CtlT e pc (Lbl l a)

ifc_protect :: Monad e => a -> IFC e pc l a
ifc_protect x = UnsafeIFC $ return (MkLbl x)

ifc_lift :: Monad e => Lbl l a -> IFC e pc l a
ifc_lift  x = UnsafeIFC $ return x

ifc_lbind :: (Monad e, l ⊑ l', l ⊑ pc) => Lbl l a -> (a -> IFC e pc l' b) -> IFC e pc' l' b
ifc_lbind x f = UnsafeIFC $ runIFC $ f $ unsafeRunLbl x

ifc_apply :: (Monad e, pc ⊑ pc') => IFC e pc l a -> (Lbl l a -> IFC e pc' l' b) -> IFC e pc' l' b
ifc_apply x f = UnsafeIFC $ do a <- runIFC x
                               runIFC $ f a

ifc_assume :: (Monad e, pc ≽ (I q ∧ (∇) q), (∇) p ≽ (∇) q) =>
            (p :≽ q) -> ((p ≽ q) => IFC e pc l a) -> IFC e pc l a
ifc_assume pf m = unsafeAssume pf m

instance Monad e => FLAMonad (CtlT e) Lbl where
  protect = ifc_protect
  lift    = ifc_lift 
  lbind   = ifc_lbind
  apply   = ifc_apply
  assume  = ifc_assume
