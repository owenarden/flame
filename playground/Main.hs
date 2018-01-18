{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Main where

import Data.Int
import Data.Functor.Identity
import Text.PrettyPrint.Mainland

import Control.Monad.Operational.Higher (singleInj, reexpress, (:+:))

import Language.Embedded.Expression
--import Language.Embedded.Imperative
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Language.Embedded.Signature
import Language.C.Monad 
--import Language.Embedded.Imperative.CMD (RefCMD (GetRef))

import Flame.EDSL.IFC
import Flame.EDSL.CMD
import Flame.EDSL.Frontend
import Flame.Principals
import Flame.Runtime.Principals

class    (Eq a, Ord a, Show a, CType a) => Type a
instance (Eq a, Ord a, Show a, CType a) => Type a

data HighExp a where
  HVar  :: Type a => VarId -> HighExp a
  HLit  :: Type a => a -> HighExp a

  HAdd  :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HMul  :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a

  HNot  :: HighExp Bool -> HighExp Bool
  HEq   :: Type a => HighExp a -> HighExp a -> HighExp Bool

  --HInjL  :: (Type a, Type b) => HighExp a -> HighExp (Either a b)
  --HInjR  :: (Type a, Type b) => HighExp b -> HighExp (Either a b)
  --HCase  :: (Type a, Type b, Type c) => HighExp (Either a b)
  --                                      -> (HighExp a -> HighExp c)
  --                                      -> (HighExp b -> HighExp c)
  --                                      -> HighExp c

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

transHighExp :: forall exp pc a. HighExp a -> Prog CMD CExp pc (CExp a)
transHighExp (HVar v)    = return (varExp v)
transHighExp (HLit a)    = return (constExp a)
transHighExp (HAdd a b)  = (+)   <$> transHighExp a <*> transHighExp b
transHighExp (HMul a b)  = (*)   <$> transHighExp a <*> transHighExp b
transHighExp (HNot a)    = not_  <$> transHighExp a
transHighExp (HEq a b)   = (#==) <$> transHighExp a <*> transHighExp b

instance HasCBackend CMD HighExp pc where
  transExp e = do
    cexp <- transHighExp e
    return $ evalCExp cexp

powerInput :: Prog CMD (LAB Label HighExp KBot KBot) KBot ()
powerInput = do
  printf "Please enter two numbers\n"
  printf " > "; m :: (LAB Label HighExp KBot KBot) Int32 <- fget stdin
  printf "m: %d\n" m
  printf " > "; n :: (LAB Label HighExp KBot KBot) Int32 <- fget stdin
  printf "n: %d\n" n
  printf "m*n = %d\n" $
    use m $ \m' -> use n $ \n' -> protect (m'*n')

main = undefined --do
--  putDoc $ case (compileLAB "main" powerInput) of
--              [(s,d)] -> d
              
--main = runCompiled $ reexpress (transLAB @CMD) powerInput