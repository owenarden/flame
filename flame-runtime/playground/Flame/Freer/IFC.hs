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

-- | Lift an effect into the freer monad.
toFreer :: f a -> Freer f a
toFreer eff = Do eff Return

-- | Interpret the effects in a freer monad in terms of another monad.
interpFreer :: Monad m => (forall a. f a -> m a) -> Freer f a -> m a
interpFreer handler (Return a) = return a
interpFreer handler (Do eff k) = handler eff >>= interpFreer handler . k
-- -- | Type list membership test.
-- type family Find x ys where
--     Find x '[]       = 'False
--     Find x (x ': ys) = 'True
--     Find x (y ': ys) = Find x ys
-- 
-- data Find'' :: TyFun k (TyFun [k] Bool -> *) -> * where
--     Find'' :: Find'' f
-- 
-- data Find' :: k -> TyFun [k] Bool -> * where
--     Find' :: Find' x f
-- 
-- type instance Apply Find'' x = Find' x
-- type instance Apply (Find' x) xs = Find x xs
-- 
-- -- | Instance resolution for this class fails with a custom type error
-- -- if @t :: * -> *@ is in the list @r :: [* -> *]@.
-- class IfDupFound (t :: Type -> Type) (r :: [Type -> Type]) (w :: [Type -> Type])
-- 
-- -- | If we reach an empty list, that’s a success, since it means the type isn’t
-- -- in the list. For GHC >=8, we can render a custom type error that explicitly
-- -- states what went wrong.
-- instance IfDupFound t '[] w
-- instance TypeError ('Text "‘" ':<>: 'ShowType (Labeled pc')
--                     ':<>: 'Text "’ is a duplicate member of the type-level list"
--                     ':$$: 'Text "  ‘" ':<>: 'ShowType w ':<>: 'Text "’"
--                     ':$$: 'Text "In the constraint ("
--                     ':<>: 'ShowType (Labeled pc) ':<>: 'Text ")"
--                     ) 
--                     => IfDupFound (Labeled pc') ((Labeled pc') ': r) w
-- instance {-# OVERLAPPABLE #-} IfDupFound (Labeled pc) r w => IfDupFound (Labeled pc) (t' ': r) w
-- 
-- class (Member (Labeled pc) effs) => LabeledMember (pc :: KPrin) effs where

---- | Base case; element is at the current position in the list and nowhere else.
--instance (Member (Labeled (pc::KPrin)) ((Labeled pc) ': r)) => --, IfDupFound (Labeled pc') r r) => 
--    LabeledMember pc ((Labeled pc) ': r) where
--
---- | Recursion; element is not at the current position, but is somewhere in the
---- list.
--instance {-# INCOHERENT #-} (LabeledMember pc r) => LabeledMember pc (t' ': r) where

-- instance (Member (Labeled pc) r) => LabeledMember pc r where


data (l::KPrin) ! a  where
  Label :: a  -> l!a

type Use pc = forall pc a l. (l⊑pc) => (l ! a) -> a

data LabeledSig m (pc::KPrin) a where 
    LReturn :: (pc ⊑ l) => a -> LabeledSig m pc (l!a)
    LBind :: (l ⊑ l') => l!a -> (a -> Labeled m pc (l'!b)) -> LabeledSig m pc (l'!b)

type Labeled m pc = Freer (LabeledSig m pc)
-- data Labeled (pc::KPrin) a where 
--     Return :: forall pc l a. (pc ⊑ l) => a -> Labeled pc (l!a)
--     Bind :: forall pc l l' a b. (l ⊑ l', l ⊑ pc) => l!a -> (a -> Labeled pc (l'!b)) -> Labeled pc (l'!b)
-- 
lreturn :: (pc ⊑ l) => a -> Eff effs (l!a)
lreturn a = send (Return @pc @l a)
-- 
-- lbind :: forall pc l l' a b effs. (Member (Labeled pc) effs, l ⊑ l', l ⊑ pc) => l!a -> (a -> Labeled pc (l'!b)) -> Eff effs (l'!b)
-- lbind la k = send (Bind @pc @l @l' la k)
-- 
-- runLabeled :: forall pc effs. Eff ((Labeled pc) ': effs) ~> Eff effs
-- runLabeled = interpret $ \case
--               Return a -> pure $ Label a
--               Bind (Label a) k -> pure $ (exec $ k a)
--   where 
--     exec :: Labeled pc (l'!b) -> (l'!b)
--     exec = \case 
--               Return a -> Label a
--               Bind (Label a) k -> exec $ k a

--- relabel :: forall pc l l' a effs. (Member (Labeled pc) effs, l ⊑ l') => Eff effs (l!a) -> Eff effs (l'!a)
--- relabel ela = do
---   la <- ela
---   lbind @pc @l @l' la (\a -> lreturn @pc @l' a)
--- 
--  Return _ _ a -> lreturn pc l'
    -- evl <- e
  -- send (bind pc l l' evl (\a -> Main.return pc l' a))

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

main :: IO ()
main = undefined