{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

import Flame.Principals
import Control.Monad.Freer
import Data.Type.Bool
import Data.Proxy (Proxy(..))
import Data.Kind (Type)
import Data.Constraint
import Data.OpenUnion.Internal
import Data.Constraint.Unsafe
import Data.Reflection
-- import Data.Singletons (Apply, TyFun)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import System.IO
import Control.Monad ((>=>))

-- | Freer monads.
--
-- A freer monad @Freer f a@ represents an effectful computation that returns a
-- value of type @a@. The parameter @f :: * -> *@ is a effect signature that
-- defines the effectful operations allowed in the computation. @Freer f a@ is
-- called a freer monad in that it's a `Monad` given any @f@.
data Freer f a where
  -- | A pure computation.
  Return :: a -> Freer f a
  -- | An effectful computation where the first argument @f b@ is the effect
  -- to perform and returns a result of type @b@; the second argument
  -- @b -> Freer f a@ is a continuation that specifies the rest of the
  -- computation given the result of the performed effect.
  Do :: f b -> (b -> Freer f a) -> Freer f a

instance Functor (Freer f) where
  fmap f (Return a) = Return (f a)
  fmap f (Do eff k) = Do eff (fmap f . k)

instance Applicative (Freer f) where
  pure = Return
  (Return f) <*> a = fmap f a
  (Do eff k) <*> a = Do eff $ (<*> a) . k

instance Monad (Freer f) where
  (Return a) >>= f = f a
  (Do eff k) >>= f = Do eff (k >=> f)

-- | Interpret the effects in a freer monad in terms of another monad.
interpFreer :: Monad m => (forall a. f a -> m a) -> Freer f a -> m a
interpFreer handler (Return a) = return a
interpFreer handler (Do eff k) = handler eff >>= interpFreer handler . k

-- | Lift an effect into the freer monad.
toFreer :: f a -> Freer f a
toFreer eff = Do eff Return

-- instance (Member (Labeled pc) r) => LabeledMember pc r where
data (l::KPrin) ! a  where
  Seal :: { unseal :: a }  -> l!a

type Clearance pc = forall a l. (l ⊑ pc) => l!a -> a

-- type Use pc = forall pc a l. (l⊑pc) => (l ! a) -> a
data LabeledSig m (pc::KPrin) a where 
    Restrict :: Monad m => SPrin pc -> (Clearance pc -> m a) -> LabeledSig m pc (pc!a)
    Protect  :: (Monad m, pc ⊑ l) => a -> LabeledSig m pc (l!a)
    Use      :: (Monad m, l' ⊑ l, l' ⊑ pc') => 
      l'!b -> (b -> Labeled m pc' (l!a)) -> LabeledSig m pc (l!a)

type Labeled m pc = Freer (LabeledSig m pc)
 
restrict :: Monad m => SPrin pc -> (Clearance pc -> m a) -> Labeled m pc (pc!a)
restrict pc ma = toFreer (Restrict pc ma)

protect :: (Monad m, pc ⊑ l) => a -> Labeled m pc (l!a)
protect a = toFreer (Protect a)

use :: (Monad m, l' ⊑ l, l' ⊑ pc') => l'!b -> (b -> Labeled m pc' (l!a)) -> Labeled m pc (l!a)
use b k = toFreer (Use b k)

lfmap :: (Monad m, l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l') => 
    (a -> b) -> l!a -> Labeled m pc (l'!b)
lfmap f x = use x (protect . f)

relabel :: (Monad m, l ⊑ l', pc ⊑ l') => l!a -> Labeled m pc (l'!a)
relabel = lfmap id 

relabel' :: (Monad m, l ⊑ l', pc ⊑ l') => Labeled m pc (l!a) -> Labeled m pc (l'!a)
relabel' e = e >>= relabel

runLabeled :: Monad m => Labeled m pc a -> m a
runLabeled = interpFreer handler
  where
    handler :: Monad m => forall a. LabeledSig m pc a -> m a
    handler (Restrict pc ma) = ma unseal >>= (return . Seal)
    handler (Protect a) = pure (Seal a)
    handler (Use (Seal b) k)  = runLabeled $ k b 

chooseSecret :: -- (l ⊑ pc, l' ⊑ pc) => 
    SPrin l -> l!Bool -> l!Int -> l!Int -> Labeled IO pc (l!())
chooseSecret pc lb n1 n2 = use lb 
     (\b ->  if b then
                 relabel' $ s_putStrLn n1 
             else 
                 relabel' $ s_putStrLn n2)
   where 
     s_putStrLn la = restrict pc (\un -> putStrLn (show (un la)))
        

type Alice = KName "Alice"
alice :: SPrin Alice
alice = SName (Proxy :: Proxy "Alice")
main :: IO (Alice!())
main = runLabeled $ chooseSecret alice (Seal True) (Seal 1) (Seal 2)

{-
  A type class representing the assumption context.
  Delegations are added to the assumption context via 'using'
-}
class Pi del where

instance Reifies s (Def Pi a) => Pi (Lift Pi a s) where

{- Allow proofs to derive from dynamic relationships -}
newtype Lift (p :: * -> Constraint) (a :: *) (s :: *) = Lift { lower :: a }


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
(≽) :: SPrin p -> SPrin q -> (p :≽ q)
(≽) p q = Del p q

(=>=) :: SPrin p -> SPrin q -> Def Pi (AFType p q)
(=>=) = (≽)

(⊑) :: SPrin p -> SPrin q -> Def Pi (AFType (C q ∧ I p) (C p ∧ I q))
(⊑) p q = ((q*→) *∧ (p*←)) ≽ ((p*→) *∧ (q*←))

(<:) :: SPrin p -> SPrin q -> Def Pi (AFType (C q ∧ I p) (C p ∧ I q))
(<:) = (⊑)

infix 5 ≽,=>=,⊑,<:

data a :===: b where
  Equiv :: (a === b) => a :===: b

data a :≽: b where
  ActsFor :: (a ≽ b) => a :≽: b

eq :: DPrin p -> DPrin q -> Maybe (p :===: q)
eq p q | (dyn p) == (dyn q) =
  unsafeAssume ((st p) ≽ (st q)) $
    unsafeAssume ((st q) ≽ (st p)) $ Just Equiv
eq p q = Nothing

