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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.EDSL.IFC where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Flame.Principals
-- import Flame.TCB.Assume
import Data.Int
import Data.Functor.Identity
import Text.PrettyPrint.Mainland

{- EDSL imports -}
import Control.Monad.Operational.Higher
import qualified Control.Monad.State as CMS
import Control.Monad.State.Class

import Language.C.Quote.C
import qualified Language.C.Syntax as C

import Language.C.Monad hiding (inModule)
import qualified Control.Monad.Reader as R
import Language.Embedded.Expression
--import Language.Embedded.Imperative hiding (cedecl, RefCMD, Ref)
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Language.Embedded.Traversal
--import Language.Embedded.Imperative.CMD (RefCMD (GetRef), mkParam, mapFunArg, mapFunArgM)

import Flame.Principals
import Flame.EDSL.CMD
import Flame.EDSL.Frontend

data Label exp (l::KPrin) a where
  Label   :: FreePred (Label exp l) a => exp a -> Label exp l a
  Unlabel :: (FreePred (Label exp l) a, FreePred exp b, l ⊑ l')
          => Label exp l a -> (exp a -> Label exp l' b) -> Label exp l' b

data LAB (n :: (* -> *) -> KPrin -> * -> *) exp (pc :: KPrin) (l :: KPrin) a where
  Lift  :: FreePred (LAB Label exp pc l) a
        => n exp l a -> LAB n exp pc l a
  Apply :: (FreePred (LAB Label exp pc l) a {-, FreePred (LAB Label exp pc l) b-}, pc ⊑ pc', pc ⊑ pc'')
        => LAB n exp pc l a -> (n exp l a -> LAB n exp pc' l' b) -> LAB n exp pc'' l' b
  Bind  :: (FreePred (LAB Label exp pc l) a, FreePred (LAB Label exp pc l) b, l ⊑ l', l ⊑ pc')
        => n exp l a -> (exp a -> LAB n exp pc' l' b) -> LAB n exp pc l' b

type Prog instr exp pc a = Program instr (Param3 exp CType pc) a

class    (FreePred exp a, Eq a, Ord a, Show a, CType a, ToExp a) => LABType exp a
instance (FreePred exp a, Eq a, Ord a, Show a, CType a, ToExp a) => LABType exp a

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

class HasCBackend instr exp pc where
  transExp :: exp a -> Prog instr CExp pc a

-- Idea: FLA monad for Program? Running yields a labeled program?
transLabel :: (HasCBackend instr exp pc, FreeExp exp, RefCMD :<: instr)
           => Label exp l a -> Prog instr CExp pc a
transLabel (Label v) = transExp v 
transLabel (Unlabel lv f) = do 
  r  <- initRef =<< (value <$> transLabel lv)
  a' <- singleInj $ GetRef r
  transLabel $ f $ valToExp a'

{-
transLAB :: forall instr exp pc l a.
            (HasCBackend instr exp pc, FreeExp exp, RefCMD :<: instr)
         => LAB Label exp pc l a -> Prog instr CExp pc (CExp a)
transLAB (Lift lv) = transLabel lv 
transLAB (Bind lv f) = undefined
  --do
  -- insight: this fails b/c CMD pc cannot "go back down". maybe need to scope refs?
  -- OR: the labeled value never gets explicitly unlabeled.. GetRef seems a little fishy
  --  r  <- initRef =<< transLabel lv
  --  a' <- singleInj $ GetRef r
  --  transLAB $ f $ valToExp a'
transLAB (Apply lv f) = undefined
--transLAB (Apply lv f) =  do 
--  r  <- initRef =<< transLAB lv
--  a' <- singleInj $ GetRef r
--  transLAB $ f $ valToExp a'
-}

{-
compileLAB :: forall instr exp pc l a.
              ( HasCBackend instr exp pc
              , Reexpressible instr instr ()
              , Interp instr CGen (Param3 CExp CType pc)
              , FreeExp exp, RefCMD :<: instr
              )
           => String -> Prog instr (LAB Label exp pc l) pc a -> [(String,Doc)]
compileLAB s = prettyCGen . wrapFunc s . (interpret :: Prog instr CExp pc a -> CGen a) . reexpress @instr transLAB

wrapFunc s prog = do
    (_,uvs,params,items) <- inNewFunction $ prog >> addStm [cstm| return 0; |]
    setUsedVars s uvs
    addGlobal [cedecl| int $id:s($params:params){ $items:items }|]
-}

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

newtype LCode n instr exp pc l a = LCode { code :: CGen a }

compile_lift :: forall instr exp pc l a.
             ( HasCBackend instr exp pc
             , FreeExp exp
             , HFunctor instr
             , Interp instr CGen (Param3 CExp CType pc)
             , RefCMD :<: instr
             , pc ⊑ l
             ) => Label exp l a -> LCode Label instr CExp pc l a
compile_lift v = LCode $ interpret (transLabel v :: Prog instr CExp pc a)

compile_apply ::( HasCBackend instr exp pc
             , LABType exp a
             , FreeExp exp
             , HFunctor instr
             , Interp instr CGen (Param3 CExp CType pc)
             , RefCMD :<: instr
             , pc ⊑ pc', pc ⊑ pc''
             ) => LCode Label instr CExp pc l a -> (Label exp l a -> LCode Label instr CExp pc' l' b) -> LCode Label instr CExp pc'' l' b
compile_apply (LCode v) f = LCode $ do
  (a, bodyc) <- inNewBlock $ do
                  vexp  <- v
                  x <- freshVar (Proxy :: Proxy CType)
                  addStm  [cstm| $id:x = $vexp; |]
                  case (f $ valToExp x) of
                    LCode res -> res
  addStm [cstm|{ $items:bodyc }|]
  return a

compile_bind :: forall instr exp pc pc' l l' a b.
             ( HasCBackend instr exp pc
             , LABType exp a
             , FreeExp exp
             , HFunctor instr
             , Interp instr CGen (Param3 CExp CType pc)
             , RefCMD :<: instr
             , l ⊑ l', l ⊑ pc
             ) => Label exp l a -> (exp a -> LCode Label instr CExp pc l' b) -> LCode Label instr CExp pc' l' b
compile_bind v f = LCode $ do
  (a, bodyc) <- inNewBlock $ do
                  vexp  <- interpret (transLabel v :: Prog instr CExp pc a)
                  x <- freshVar (Proxy :: Proxy CType)
                  addStm  [cstm| $id:x = $vexp; |]
                  case (f $ valToExp x) of
                    LCode res -> res
  addStm [cstm|{ $items:bodyc }|]
  return a