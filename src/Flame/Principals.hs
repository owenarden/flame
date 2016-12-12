{-# LANGUAGE GADTs, PolyKinds, DataKinds, RankNTypes #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Flame.Principals
       ( KPrin (..)
       , SPrin (..)
       , C, I, type (^->), type (^→), type (^<-), type (^←)
       , N, Public, Secret, Trusted, Untrusted, PT, SU 
       , DPrin (st, dyn) 
       , withPrin
       , type (/\), type (∧), type (\/), type (∨) 
       , type (⊔), type (⊓)
       , type (≽), type (>=), type (⊑), type (<:), type (===)
       , type (∇), Voice, Δ, Eye, (∇), δ 
       , (⊤), top, (⊥), bot
       , public, trusted, publicTrusted, secret, untrusted, secretUntrusted
       , (^->), (^→), (^<-), (^←)
       , (/\), (∧), (\/), (∨), (⊔), (⊓)
       , (*->), (*→), (*<-), (*←), (*/\), (*∧), (*\/), (*∨), (*⊔), (*⊓), (*∇)  
       )
where

import Data.Constraint hiding (top)
import GHC.TypeLits
import Data.Proxy (Proxy(..))
import Data.Type.Bool
import Data.Data

import Flame.Runtime.Principals

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
  | KEye   KPrin

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
  SEye   :: SPrin p -> SPrin (KEye   p)

deriving instance Show (SPrin p)
deriving instance Eq (SPrin p)

{- Some notation help -}
type C p      = KConf p
type (^→) p  = KConf p
type (^->) p  = KConf p
type I p      = KInteg p
type (^←) p  = KInteg p
type (^<-) p  = KInteg p
type Voice p  = KVoice p
type Eye p    = KEye p
type N s      = KName s

type (/\) p q = KConj p q
type p ∧ q  = KConj p q
infixl 7 /\
infixl 7 ∧

type (\/) p q = KDisj p q
type (∨)  p q = KDisj p q
infixl 7 ∨

type (∇) p = Voice p
type (Δ) p = Eye p

-- TODO: convert flow join/meet to type families so that
--       resulting types are more normalized
type (⊔) p q  = (C p ∧ C q) ∧ (I p ∨ I q)
infixl 6 ⊔
type (⊓) p q  = (C p ∨ C q) ∧ (I p ∧ I q)
infixl 6 ⊓

type (⊤) = KTop
type (⊥) = KBot
type Public   = C KBot
type Trusted  = I KTop
type PT       = Public ∧ Trusted 

type Secret = C KTop
type Untrusted  = I KBot
type SU       = Secret ∧ Untrusted

(*->) p   = SConf p
(*→)  p   = SConf p

(*<-) p   = SInteg p
(*←) p   = SInteg p

(*∇)  p = SVoice p

(*/\) p q  = SConj p q
(*∧)  p q  = SConj p q

(*\/) p q  = SDisj p q
(*∨)  p q  = SDisj p q

(*⊔)  p q  = ((p*→) *∧ (q*→)) *∧ ((p*←) *∨ (q*←))
(*⊓)  p q  = ((p*→) *∨ (q*→)) *∧ ((p*←) *∧ (q*←))

public :: SPrin Public
public = SConf SBot
trusted  :: SPrin Trusted
trusted  = SInteg STop
publicTrusted :: SPrin PT
publicTrusted = public *∧ trusted

secret :: SPrin Secret
secret = (SConf STop)
untrusted  :: SPrin Untrusted
untrusted  = (SInteg SBot)
secretUntrusted :: SPrin SU
secretUntrusted = secret *∧ untrusted

{- Existential wrapper -}
data Ex (p :: k -> *) where
  Ex :: p i -> Ex p

{- Promote runtime principals to existentially-wrapped principal types -}
promote :: Prin -> Ex SPrin
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

{- Bind runtime principal to type -}
withPrin :: Prin -> (forall p . DPrin p -> a) -> a
withPrin p f = case promote p of
                 Ex p' -> f (p <=> p') 

-- do not export <=> or UnsafeBindP. This ensures only withPrin can associate
--  runtime principals wth singleton principal types.
data DPrin p = UnsafeAssoc { dyn :: Prin, st :: SPrin p } 
dynamic = dyn
static = st 
(<=>) :: Prin -> SPrin p -> DPrin p
p <=> sp = UnsafeAssoc p sp

(⊤) :: DPrin (⊤)
(⊤) = Top <=> STop
top = (⊤)

(⊥) :: DPrin (⊥)
(⊥) = Bot <=> SBot
bot = (⊥)

(^→) :: DPrin p  -> DPrin (C p)
(^→) p  = Conf (dyn p) <=> SConf (st p)
(^->) = (^→)

(^←) :: DPrin p  -> DPrin (I p)
(^←) p = Integ (dyn p) <=> SInteg (st p)
(^<-) = (^←)

(∧) :: DPrin p -> DPrin q -> DPrin (p ∧ q) 
(∧) p q = Conj (dyn p) (dyn q) <=> SConj (st p) (st q)
(/\) = (∧)

(∨) :: DPrin p -> DPrin q -> DPrin (p ∨ q) 
(∨)  p q  = Disj (dyn p) (dyn q) <=> SDisj (st p) (st q)
(\/) = (∨)

(⊔) :: DPrin p -> DPrin q -> DPrin (p ⊔ q) 
(⊔)  p q  = (Conj (Conf (Conj (dyn p) (dyn q)))
             (Integ (Disj (dyn p) (dyn q)))) <=> ((st p) *⊔ (st q))
join = (⊔)

(⊓) :: DPrin p -> DPrin q -> DPrin (p ⊓ q) 
(⊓) p q  = (Conj (Conf (Disj (dyn p) (dyn q)))
            (Integ (Conj (dyn p) (dyn q)))) <=> ((st p) *⊓ (st q))
meet = (⊓)

(∇) :: DPrin p -> DPrin ((∇) p)
(∇) p = voiceOf (dyn p) <=> SVoice (st p)
        
δ :: DPrin p -> DPrin (Δ p)
δ p = eyeOf (dyn p) <=> SEye (st p)

{- Actsfor constraint -}
{- Exported type operators for actsfor -}
type family (≽) (p :: KPrin) (q :: KPrin) :: Constraint where

type (>=) (p :: KPrin) (q :: KPrin) = (p ≽ q) 

{- Exported type operators for flowsto -}
type (⊑) (p :: KPrin) (q :: KPrin) = (C q ≽ C p , I p ≽ I q) 
type (<:) (p :: KPrin) (q :: KPrin) = (p ⊑ q)
-- This doesn't work somehow..
type (===) (p :: KPrin) (q :: KPrin) = (p ≽ q, q ≽ p)
