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
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.EDSL.IFC where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection
import Data.Functor.Identity 

import Flame.Principals
-- import Flame.TCB.Assume
import Data.Int
import Data.Functor.Identity

{- EDSL imports -}
import Control.Monad.Operational.Higher (singleInj, reexpress, Reexpressible, Interp)
import Language.C.Monad
import Language.Embedded.Expression
import Language.Embedded.Imperative
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Language.Embedded.Imperative.CMD (RefCMD (GetRef))

import Flame.Principals

data Label exp (l::KPrin) a where
  Label   :: FreePred (Label exp l) a => exp a -> Label exp l a
  Unlabel :: (FreePred (Label exp l) a, FreePred exp b, l ⊑ l')
          => Label exp l a -> (exp a -> Label exp l' b) -> Label exp l' b

data LAB (n :: (* -> *) -> KPrin -> * -> *) exp (pc :: KPrin) (l :: KPrin) a where
  Lift  :: FreePred (LAB Label exp pc l) a
        => n exp l a -> LAB n exp pc l a
  Apply :: (FreePred (LAB Label exp pc l) a, FreePred (LAB Label exp pc l) b, pc ⊑ pc', pc ⊑ pc'')
        => LAB n exp pc l a -> (n exp l a -> LAB n exp pc' l' b) -> LAB n exp pc'' l' b
  Bind  :: (FreePred (LAB Label exp pc l) a, FreePred (LAB Label exp pc l) b, l ⊑ l', l ⊑ pc')
        => n exp l a -> (exp a -> LAB n exp pc' l' b) -> LAB n exp pc l' b

type Prog instr exp a = Program instr (Param2 exp CType) a

class    (FreePred exp a, Eq a, Ord a, Show a, CType a) => LABType exp a
instance (FreePred exp a, Eq a, Ord a, Show a, CType a) => LABType exp a

instance FreeExp exp => FreeExp (Label exp l)
  where
    type FreePred (Label exp l) = LABType exp
    constExp c = Label $ constExp c
    varExp   v = Label $ varExp v

instance FreeExp exp => FreeExp (LAB Label exp pc l)
  where
    type FreePred (LAB Label exp pc l) = LABType exp
    constExp c = Lift $ (Label $ constExp c)
    varExp   v = Lift $ (Label $ varExp v)

class HasCBackend instr exp where
  transExp :: exp a -> Prog instr CExp (CExp a)

transLabel :: (HasCBackend instr exp, FreeExp exp, RefCMD :<: instr)
           => Label exp l a -> Prog instr CExp (CExp a)
transLabel (Label v) = transExp v 
transLabel (Unlabel lv f) = do 
  r  <- initRef =<< transLabel lv
  a' <- singleInj $ GetRef r
  transLabel $ f $ valToExp a'

transLAB :: forall instr exp pc l a.
            (HasCBackend instr exp, FreeExp exp, RefCMD :<: instr)
         => LAB Label exp pc l a -> Prog instr CExp (CExp a)
transLAB (Lift lv) = transLabel lv 
transLAB (Bind (lv :: Label exp l' b) f) =  do 
  r  <- initRef =<< transLabel lv
  a' <- singleInj $ GetRef r
  transLAB $ f $ valToExp a'
transLAB (Apply lv f) =  do 
  r  <- initRef =<< transLAB lv
  a' <- singleInj $ GetRef r
  transLAB $ f $ valToExp a'

compileLAB :: forall instr exp pc l a.
              ( HasCBackend instr exp
              , Reexpressible instr instr ()
              , Interp instr CGen (Param2 CExp CType)
              , FreeExp exp, RefCMD :<: instr
              )
           => Prog instr (LAB Label exp pc l) a -> String
compileLAB = (compile :: Prog instr CExp a -> String) . reexpress transLAB

class Labeled (n :: (* -> *) -> KPrin -> * -> *) exp where
  label   :: LABType exp a => exp a -> n exp l a
  unlabel :: (LABType exp a, LABType exp b, l ⊑ l') => n exp l a -> (exp a -> n exp l' b) -> n exp l' b
  relabel :: (LABType exp a, l ⊑ l') => n exp l a -> n exp l' a
  relabel a = unlabel a label 

instance Labeled Label exp where
  label   = Label
  unlabel = Unlabel

class Labeled n exp => IFC (m :: ((* -> *) -> KPrin -> * -> *)
                                   -> (* -> *) -> KPrin -> KPrin -> * -> *)
                                 n exp where
  lift   :: (LABType exp a, pc ⊑ l) => n exp l a -> m n exp pc l a

  apply  :: (LABType exp a, LABType exp b, pc ⊑ pc', pc ⊑ pc'')
         => m n exp pc l a -> (n exp l a -> m n exp pc' l' b) -> m n exp pc'' l' b

  bind   :: (LABType exp a, LABType exp b, l ⊑ l', l ⊑ pc)
         => n exp l a -> (exp a -> m n exp pc l' b) -> m n exp pc' l' b

  protect :: (LABType exp a, pc ⊑ l) => exp a -> m n exp pc l a
  protect = lift . label

  use :: forall l l' pc pc' pc'' a b.
         (LABType exp a, LABType exp b, l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'')
      => m n exp pc l a -> (exp a -> m n exp pc' l' b) -> m n exp pc'' l' b
  use x f = apply x $ \x' -> (bind x' f :: m n exp pc' l' b)
 
  reprotect :: forall l l' pc pc' a.
               (LABType exp a, l ⊑ l', pc ⊑ pc', (pc ⊔ l) ⊑ l')
            => m n exp pc l a -> m n exp pc' l' a 
  reprotect x = use x (protect :: exp a -> m n exp (pc ⊔ l) l' a)

  ifmap :: forall l l' pc pc' a b.
           (LABType exp a, LABType exp b, l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l')
        => (exp a -> exp b) -> m n exp pc l a -> m n exp pc' l' b
  ifmap f x = use x (\x' -> protect (f x') :: m n exp (pc ⊔ l) l' b)

instance IFC LAB Label exp where
  lift = Lift
  apply = Apply
  bind = Bind