{-# LANGUAGE GADTs, PolyKinds, DataKinds, RankNTypes #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Flame.Type.Principals
where
import Data.Constraint
import GHC.TypeLits
import Data.Proxy (Proxy(..))
import Data.Type.Bool
import Data.Data

import Flame.Data.Principals

{- The principal kind -}
data KPrin =
  KTop
  | KBot
  | KName  Symbol 
  | KConj  KPrin KPrin 
  | KDisj  KPrin KPrin
  | KConf  KPrin
  | KInteg KPrin
  | KVoice KPrin

{- Singleton GADT for KPrin -}
data SPrin :: KPrin -> * where
  STop   :: SPrin KTop
  SBot   :: SPrin KBot
  SName  :: forall (n :: Symbol). Proxy n -> SPrin (KName n)
  SConj  :: SPrin p -> SPrin q -> SPrin (KConj p q)
  SDisj  :: SPrin p -> SPrin q -> SPrin (KDisj p q)
  SConf  :: SPrin p -> SPrin (KConf p)
  SInteg :: SPrin p -> SPrin (KInteg p)
  SVoice :: SPrin p -> SPrin (KVoice p)

deriving instance Show (SPrin p)
deriving instance Eq (SPrin p)

{- Existential wrapper -}
data Ex (p ::k -> *) where
  Ex :: p i -> Ex p

--{- Existential type-level principals -}
type WPrin = Ex SPrin

{- Promote runtime principals to existentially-wrapped principal types -}
promote :: Prin -> WPrin
promote p =
  case p of
    Top         ->  Ex STop
    Bot         ->  Ex SBot
    (Name str)  ->  case someSymbolVal str of
                      SomeSymbol n -> Ex (SName n)
    (Conj p q)  ->  case promote p of
                      Ex p' -> case promote q of
                                 Ex q' -> Ex (SConj p' q')
    (Disj p q)  ->  case promote p of
                      Ex p' -> case promote q of
                                 Ex q' -> Ex (SDisj p' q')
    (Conf p)    ->  case promote p of Ex p' -> Ex (SConf p')
    (Integ p)   ->  case promote p of Ex p' -> Ex (SInteg p')
--    (Voice p)   ->  case promote p of Ex p' -> Ex (SVoice p')

{- Some notation help -}
type C p      = KConf p
type I p      = KInteg p
type Voice p  = KVoice p
type N s      = KName s

type (/\) p q = KConj p q
type (∧)  p q  = KConj p q
infixl 7 /\
infixl 7 ∧

type (\/) p q = KDisj p q
type (∨)  p q = KDisj p q
infixl 7 ∨

-- TODO: convert flow join/meet to type families so that
--       resulting types are more normalized
type (⊔) p q  = ((C p) ∧ (C q)) ∧ ((I p) ∨ (I q))
infixl 6 ⊔
type (⊓) p q  = ((C p) ∨ (C q)) ∧ ((I p) ∧ (I q))
infixl 6 ⊓

type Public   = C KBot
type Trusted  = I KTop
type PT       = Public ∧ Trusted 

type Secret = C KTop
type Untrusted  = I KBot
type SU       = Secret ∧ Untrusted

(^->) p   = SConf p
(^→)  p   = SConf p
(^<-) p   = SInteg p
(^←) p   = SInteg p
voice p   = SVoice p
(/\) p q  = SConj p q
(∧)  p q  = SConj p q

(\/) p q = SDisj p q
(∨)  p q = SDisj p q
(⊔)  p q  = ((p^→) ∧ (q^→)) ∧ ((p^←) ∨ (q^←))
(⊓)  p q  = ((p^→) ∨ (q^→)) ∧ ((p^←) ∧ (q^←))

ptop = STop
pbot = SBot
public  = SConf pbot
trusted = SInteg ptop
publicTrusted = public ∧ trusted           

-- do not export <=> or UnsafeBindP. This ensures only withPrin can associate
--  runtime principals wth singleton principal types.
data Bound p = UnsafeBindP { dyn :: Prin, st :: SPrin p } 
dynamic = dyn
static = st 
(<=>) :: Prin -> SPrin p -> Bound p
p <=> sp = UnsafeBindP p sp

{- Bind runtime principal to type -}
withPrin :: Prin -> (forall p . Bound p -> a) -> a
withPrin p f = case promote p of
                 Ex p' -> f (p <=> p') 

{- Actsfor constraint -}
{- Exported type operators for actsfor -}
type family (≽) (p :: KPrin) (q :: KPrin) :: Constraint where
  KBot ≽ KBot = (True ~ True) -- until GHC 8.x, closed families cannot be empty.

type (>=) (p :: KPrin) (q :: KPrin) = (p ≽ q) 

{- Exported type operators for flowsto -}
type (⊑) (p :: KPrin) (q :: KPrin) = ((C q ≽ C p) , (I p ≽ I q)) 
type (<:) (p :: KPrin) (q :: KPrin) = ((C q ≽ C p) , (I p ≽ I q)) 
type (===) (p :: KPrin) (q :: KPrin) = (p ≽ q, q ≽ p)
