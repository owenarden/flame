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
import Text.PrettyPrint.Mainland

import Control.Monad.Operational.Higher (singleInj, reexpress)

import Language.Embedded.Expression
import Language.Embedded.Imperative
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Language.Embedded.Signature
import Language.C.Monad 

import Flame.EDSL.IFC
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

  --HPair  :: (Type a, Type b) => HighExp a -> HighExp b -> HighExp (a,b)
  --HProjL :: (Type a, Type b) => HighExp (a, b) -> HighExp a
  --HProjR :: (Type a, Type b) => HighExp (a, b) -> HighExp b

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

instance CompExp HighExp where
  compExp = compCExp <$> compHighExp

compHighExp :: HighExp a -> CExp a
compHighExp (HVar v)   = varExp v
compHighExp (HLit a)   = constExp a
compHighExp (HAdd a b) = (compHighExp a) + (compHighExp b)
compHighExp (HMul a b) = (compHighExp a) * (compHighExp b)
compHighExp (HNot a)   = not_  (compHighExp a)
compHighExp (HEq a b)  = (compHighExp a) #== (compHighExp b)

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

main = do
  putDoc $ case (compileLAB "main" powerInput) of
              [(s,d)] -> d
              
--main = runCompiled $ reexpress (transLAB @CMD) powerInput