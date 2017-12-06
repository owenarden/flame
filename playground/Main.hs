{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Main where

import Data.Int
import Data.Functor.Identity

import Control.Monad.Operational.Higher (singleInj, reexpress)

import Language.Embedded.Expression
import Language.Embedded.Imperative
import Language.Embedded.Backend.C
import Language.Embedded.CExp

import Flame.EDSL.IFC
import Flame.Principals
import Flame.Runtime.Principals

class    (Eq a, Ord a, Show a, CType a) => Type a
instance (Eq a, Ord a, Show a, CType a) => Type a

data HighExp a where
  HVar :: Type a => VarId -> HighExp a
  HLit :: Type a => a -> HighExp a
  HAdd :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HMul :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HNot :: HighExp Bool -> HighExp Bool
  HEq  :: Type a => HighExp a -> HighExp a -> HighExp Bool

instance (Num a, Type a) => Num (HighExp a) where
  fromInteger = HLit . fromInteger
  (+) = HAdd
  (*) = HMul

instance FreeExp HighExp
  where
    type FreePred HighExp = Type
    constExp = HLit
    varExp = HVar

type CMD
    =   RefCMD      -- Mutable references
    :+: ControlCMD  -- Control structures
    :+: FileCMD     -- Input/output

transHighExp :: HighExp a -> Prog CMD CExp (CExp a)
transHighExp (HVar v)   = return (varExp v)
transHighExp (HLit a)   = return (constExp a)
transHighExp (HAdd a b) = (+)   <$> transHighExp a <*> transHighExp b
transHighExp (HMul a b) = (*)   <$> transHighExp a <*> transHighExp b
transHighExp (HNot a)   = not_  <$> transHighExp a
transHighExp (HEq a b)  = (#==) <$> transHighExp a <*> transHighExp b

instance HasCBackend CMD HighExp where
  transExp = transHighExp

powerInput :: Prog CMD (LAB Label HighExp KBot KBot) ()
powerInput = do
  printf "Please enter two numbers\n"
  printf " > "; m :: (LAB Label HighExp KBot KBot) Int32 <- fget stdin
  printf "m: %d\n" m
  printf " > "; n :: (LAB Label HighExp KBot KBot) Int32 <- fget stdin
  printf "n: %d\n" n
  printf "m*n = %d\n" $
    use m $ \m' -> use n $ \n' -> protect (m'*n')

main = putStrLn $ compileLAB powerInput

--main = runCompiled $ reexpress (transLAB @CMD) powerInput