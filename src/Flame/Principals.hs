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

module Flame.Principals
where
import GHC.TypeLits
import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection
import Data.Type.Bool

{- The principal data type -}
data Prin =
  Top
  | Bot
  | Name String
  | Conj  Prin Prin 
  | Disj  Prin Prin
  | Conf  Prin
  | Integ Prin

{- The principal kind -}
data KPrin =
  KTop
  | KBot
  | KName  Symbol 
  | KConj  KPrin KPrin 
  | KDisj  KPrin KPrin
  | KConf  KPrin
  | KInteg KPrin

{- Singleton GADT for KPrin -}
data SPrin :: KPrin -> * where
  STop   :: SPrin KTop
  SBot   :: SPrin KBot
  SName  :: forall (n :: Symbol). Proxy n -> SPrin (KName n)
  SConj  :: SPrin p -> SPrin q -> SPrin (KConj p q)
  SDisj  :: SPrin p -> SPrin q -> SPrin (KDisj p q)
  SConf  :: SPrin p -> SPrin (KConf p)
  SInteg :: SPrin p -> SPrin (KInteg p)

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
    (Integ p)   ->  case promote p of Ex p' -> Ex (SConf p')

{- Some notation help -}
type C p      = KConf p
type I p      = KInteg p
type N s      = KName s

type p :/\: q = KConj p q
type p :∧: q  = KConj p q
infixl 7 :/\:
infixl 7 :∧:

type p :\/: q = KDisj p q
type p :∨: q  = KDisj p q
infixl 7 :∨:

type L c i    = (KConf c) :∧: (KInteg i)
-- TODO: convert flow join/meet to type families so that
--       resulting types are more normalized
type p :⊔: q  = ((C p) :∧: (C q)) :∧: ((I p) :∨: (I q))
infixl 6 :⊔:
type p :⊓: q  = ((C p) :∨: (C q)) :∧: ((I p) :∧: (I q))
infixl 6 :⊓:

type Public   = C KBot
type Trusted  = I KTop
type PT       = Public :∧: Trusted 

(^->) p   = SConf p
(^→)  p   = SConf p
(^<-) p   = SInteg p
(^←)  p  = SInteg p
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

{- The internal type family for the actsfor relation -}
{- Exported type operators for actsfor -}
type family (≽) (p :: KPrin) (q :: KPrin) :: Constraint

type (>=) (p :: KPrin) (q :: KPrin) = (p ≽ q) 

{- Exported type operators for flowsto -}
type (⊑) (p :: KPrin) (q :: KPrin) = ((C q ≽ C p) , (I p ≽ I q)) 
type (<:) (p :: KPrin) (q :: KPrin) = ((C q ≽ C p) , (I p ≽ I q)) 
type (===) (p :: KPrin) (q :: KPrin) = (p ≽ q, q ≽ p)

(≽) p q = Del p q
(>=) p q = Del p q
(⊑) p q = Del ((q^→) ∧ (p^←)) ((p^→) ∧ (q^←))
(<:) p q = Del ((q^→) ∧ (p^←)) ((p^→) ∧ (q^←))

infix 5 ≽,>=,⊑

type family Voice (p :: KPrin) :: KPrin

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

{- Allow proofs to derive from dynamic relationships -}
instance Reifies s (Def Pi a) => Pi (Lift Pi a s) where

data Lift (p :: * -> Constraint) (a :: *) (s :: *) = Lift { lower :: a }

class ReifiableConstraint p where
  data Def (p :: * -> Constraint) (a :: *) :: *
  reifiedIns :: Reifies s (Def p a) :- p (Lift p a s)
 
data AFType (p :: KPrin) (q :: KPrin) = AFType { sup :: SPrin p, inf :: SPrin q}

instance ReifiableConstraint Pi where
  data Def Pi (AFType p q) = Del { sup_ :: SPrin p, inf_ :: SPrin q}
  reifiedIns = Sub Dict

-- added 'b' to allow more general computation qualified by constraint p
-- Should not be exported (directly).
using :: forall a p q. Def Pi (AFType p q) -> ((p ≽ q) => a) -> a
using d m = reify d $ \(_ :: Proxy s) ->
  let replaceProof :: Reifies s (Def Pi (AFType p q)) :- (p ≽ q)
      replaceProof = trans proof reifiedIns
        where proof = unsafeCoerceConstraint :: Pi (Lift Pi (AFType p q) s) :- (p ≽ q)
  in m \\ replaceProof
