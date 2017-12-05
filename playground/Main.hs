{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

-- This code implements the languages from EDSL_Compilation.lhs using the
-- generic imperative-edsl library.
--
-- Instead of `LowExp` we're using the existing type `CExp` from
-- imperative-edsl.
--
-- Note that this implementation produces actual C code rather than pseudo-code.

module Main where

import Data.Int
import Data.Functor.Identity

import Control.Monad.Operational.Higher (singleInj, reexpress)

import Language.Embedded.Expression
import Language.Embedded.Imperative (ProgramT, Program, Param3, Param2, (:+:))
--import Language.Embedded.Imperative.CMD (RefCMD (GetRef))
import Flame.EDSL.Backend.C
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Flame.EDSL.CMD as F
import Flame.EDSL.Frontend as F
import Flame.Principals
import Flame.Runtime.Principals

--import EDSL_Compilation (Type, HighExp (..))

class    (Eq a, Ord a, Show a, CType a) => Type a
instance (Eq a, Ord a, Show a, CType a) => Type a


data HighExp a where
  -- Simple constructs (same as in LowExp):
  HVar :: Type a => VarId -> HighExp a
  HLit :: Type a => a -> HighExp a
  HAdd :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HMul :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HNot :: HighExp Bool -> HighExp Bool
  HEq  :: Type a => HighExp a -> HighExp a -> HighExp Bool

  -- Let binding:
  Let  :: Type a
       => HighExp a                 -- value to share
       -> (HighExp a -> HighExp b)  -- body
       -> HighExp b

  -- Pure iteration:
  Iter :: Type s
       => HighExp Int32            -- number of iterations
       -> HighExp s                -- initial state
       -> (HighExp s -> HighExp s) -- step function
       -> HighExp s                -- final state

instance (Num a, Type a) => Num (HighExp a) where
  fromInteger = HLit . fromInteger
  (+) = HAdd
  (*) = HMul

type CMD
    =   F.RefCMD      -- Mutable references
    :+: F.ControlCMD  -- Control structures
    :+: F.FileCMD     -- Input/output

type Prog exp pc a = Program CMD (Param3 exp CType pc) a

instance FreeExp HighExp
  where
    type FreePred HighExp = Type
    constExp = HLit
    varExp = HVar

transHighExp :: DPrin pc -> HighExp a -> Prog CExp pc (CExp a)
transHighExp pc (HVar v)   = return (varExp v)
transHighExp pc (HLit a)   = return (constExp a)
transHighExp pc (HAdd a b) = (+)   <$> transHighExp pc a <*> transHighExp pc b
transHighExp pc (HMul a b) = (*)   <$> transHighExp pc a <*> transHighExp pc b
transHighExp pc (HNot a)   = not_  <$> transHighExp pc a
transHighExp pc (HEq a b)  = (#==) <$> transHighExp pc a <*> transHighExp pc b
transHighExp pc (Let a body) = do
  r  <- initRef =<< transHighExp pc a
  a' <- singleInj $ GetRef r
  transHighExp pc $ body $ valToExp a'
transHighExp pc (Iter n s body) = do
  n' <- transHighExp pc n
  sr <- initRef =<< transHighExp pc s
  for (0,1,Excl n') $ \_ -> do
    sPrev <- singleInj $ GetRef sr
    sNext <- transHighExp pc $ body $ valToExp sPrev
    setRef sr sNext
  getRef sr

comp :: DPrin pc -> Prog HighExp pc a -> String
comp pc = compile . reexpress (transHighExp pc)

powerInput :: Prog HighExp KBot ()
powerInput = do
  printf "Please enter two numbers\n"
  printf " > "; m :: HighExp Int32 <- fget stdin
  printf " > "; n :: HighExp Int32 <- fget stdin
  printf "Here's a fact: %d^%d = %d\n" m n (Iter n 1 (*m))

main = putStrLn $ comp bot powerInput

--main2 = runCompiled $ reexpress (transHighExp bot) powerInput
  -- Uses GCC to compile the generated code and then runs it
