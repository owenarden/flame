{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}

module Flame.TCB.Core
--       (Prin(..) , SPrin(..)
--       , C, I
--       , PT, Public, Trusted
--       , public, trusted, publicTrusted
--       , IFC, runIFC
--       , protect
--       , Lbl
--       , label
--       , unlabel
--       , flaReadFile
--       , flaRun
--       , IFCController, IFCApplication
--       )
  where

import GHC.TypeLits
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection
import Data.Type.Bool
import Data.Type.Equality hiding (trans)
  
import qualified Data.Map.Strict as Map

import Data.Proxy (Proxy(..))
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

--demote :: SPrin p -> Prin
--demote STop        = Top
--demote SBot        = Bot
----demote (SName n)   = error "Cannot demote: principal name not known statically."
--demote (SConj p q) = Conj (demote p) (demote q)
--demote (SDisj p q) = Disj (demote p) (demote q)
--demote (SConf p)   = Conf (demote p) 
--demote (SInteg p)   =Integ (demote p)

{- Some notation help -}
type C p      = KConf p
type I p      = KInteg p
type N s      = KName s
type p :/\: q = KConj p q
type p :∧: q  = KConj p q
type p :\/: q = KDisj p q
type p :∨: q  = KDisj p q
type p :⊔: q  = ((C p) :∧: (C q)) :∧: ((I p) :∨: (I q))
type p :⊓: q  = ((C p) :∨: (C q)) :∧: ((I p) :∧: (I q))
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

data AFType (p :: KPrin) (q :: KPrin) = AFType { sup :: SPrin p, inf :: SPrin q}

data FlowType (l :: KPrin) (l' :: KPrin) = FlowType { finf :: SPrin l, fsup :: SPrin l'}

{- Equivalence relationships (see prinEq is Coq proof) -}
--type family EqPrin (p::KPrin) (q::KPrin) where
--  {- Refl -}
--  EqPrin p p = True
--  {- Lattice commutativity -}
--  EqPrin (p :∧: q) (q :∧: p) = True
--  EqPrin (p :∨: q) (q :∨: p) = True
--  {- Lattice associativity (+ symmetry) -}
--  EqPrin ((p :∧: q) :∧: r) (p :∧: (q :∧: r)) = True
--  EqPrin (p :∧: (q :∧: r)) ((p :∧: q) :∧: r) = True
--  EqPrin ((p :∨: q) :∨: r) (p :∨: (q :∨: r)) = True
--  EqPrin (p :∨: (q :∨: r)) ((p :∨: q) :∨: r) = True
--  {- Lattice absorption (+ symmetry) -}
--  EqPrin (p :∧: (p :∨: q)) p = True
--  EqPrin p (p :∧: (p :∨: q)) = True
--  EqPrin (p :∨: (p :∧: q)) p = True
--  EqPrin p (p :∨: (p :∧: q)) = True
--  {- Lattice idempotence (+ symmetry) -}
--  EqPrin (p :∧: p) p = True 
--  EqPrin p (p :∧: p) = True 
--  EqPrin (p :∨: p) p = True 
--  EqPrin p (p :∨: p) = True 
--  {- Lattice identity (+ symmetry) -}
--  EqPrin (p :∧: KBot) p = True
--  EqPrin p (p :∧: KBot) = True
--  EqPrin (p :∨: KTop) p = True
--  EqPrin p (p :∨: KTop) = True
--  EqPrin (p :∧: KTop) KTop = True 
--  EqPrin KTop (p :∧: KTop) = True 
--  EqPrin (p :∨: KBot) KBot = True 
--  EqPrin KBot (p :∨: KBot) = True 
--  {- Lattice distributivity (+ symmetry) -}
--  EqPrin (p :∧: (q :∨: r)) ((p :∧: q) :∨: (p :∧: r)) = True
--  EqPrin ((p :∧: q) :∨: (p :∧: r)) (p :∧: (q :∨: r)) = True
--  {- Authority projections, property 3: distribution over conjunctions (+ symmetry) -}
--  EqPrin ((C p) :∧: (C q)) (C (p :∧: q)) = True 
--  EqPrin (C (p :∧: q)) ((C p) :∧: (C q)) = True 
--  EqPrin ((I p) :∧: (I q)) (I (p :∧: q)) = True 
--  EqPrin (I (p :∧: q)) ((I p) :∧: (I q)) = True 
--  {- Authority projections, property 4: distribution over disjunctions (+ symmetry) -}
--  EqPrin (C (p :∨: q)) ((C p) :∨: (C q)) = True 
--  EqPrin ((C p) :∨: (C q)) (C (p :∨: q)) = True 
--  EqPrin (I (p :∨: q)) ((I p) :∨: (I q)) = True 
--  EqPrin ((I p) :∨: (I q)) (I (p :∨: q)) = True 
--  {- Authority projections, property 5: idempotence (+ symmetry)-}
--  EqPrin (C (C p)) (C p) = True
--  EqPrin (C p) (C (C p)) = True
--  EqPrin (I (I p)) (I p) = True
--  EqPrin (I p) (I (I p)) = True
--  {- Basis projections, properties 2-3 (+ symmetry)-}
--  EqPrin KBot (C (I p))          = True 
--  EqPrin (I (C p)) KBot          = True
--  EqPrin KBot (I (C p))          = True
--  EqPrin ((C p) :∨: (I q)) KBot  = True
--  EqPrin KBot ((C p) :∨: (I q))  = True
--{- Admitted equivalences (+ symmetry)-}
--  EqPrin ((C p) :∧: (I p)) p = True
--  EqPrin p ((C p) :∧: (I p)) = True
--  EqPrin ((I p) :∧: (C p)) p = True
--  EqPrin p ((I p) :∧: (C p)) = True
--  EqPrin (C KBot) KBot = True 
--  EqPrin KBot (C KBot) = True 
--  EqPrin (I KBot) KBot = True 
--  EqPrin KBot (I KBot) = True 
--  EqPrin p q = False
-- Needed this rule to typecheck receive.  
-- instance AFRel (AFType p q) =>  AFRel (AFType p (p :∧: q)) where
-- Necessary?
--instance   (n1 ~ n2)   =>             AFRel (AFType (KName n1) (KName n2)) where
-- are these still needed?
--instance                              AFRel (AFType (C (I p)) (C (I q))) where
--instance                              AFRel (AFType (I (C p)) (I (C q))) where
--type instance a == b = EqPrin a b
{- Otherwise, p and q are not equal -}

data AFProof =
 AFRefl
 | AFTop
 | AFBot
 | AFProjRC
 | AFProjRI
 | AFProjC AFProof
 | AFProjI AFProof
 | AFConjL AFProof AFProof
 | AFConjR AFProof AFProof
 | AFDisjL AFProof AFProof
 | AFDisjR AFProof AFProof
 | AFTrans KPrin AFProof AFProof
 | AFFalse
class AFRel del (b::Bool) | del -> b where
{- Trans -}
-- Needs AmbiguousTypes
--instance {-# OVERLAPPABLE #-} (AFRel (AFType p q) True, AFRel (AFType q r) True) => AFRel (AFType p r) True where
{- TODO: Substitutions -}
{- ConjLR -}
instance {-# OVERLAPS #-} (AFRel (AFType p1 q1) b1, AFRel (AFType p1 q2) b2,
          AFRel (AFType p2 q1) b3, AFRel (AFType p2 q2) b4,
          ((b1 || b3) && (b2 || b4)) ~ True) => AFRel (AFType (p1 :∧: p2) (q1 :∧: q2)) True where
{- ConjLDisjR -}
instance {-# OVERLAPS #-} (AFRel (AFType p1 q1) b1, AFRel (AFType p2 q2) b2,
          AFRel (AFType p2 q1) b3, AFRel (AFType p1 q2) b4,
          (b1 || b2 || b3 || b4) ~ True) => AFRel (AFType (p1 :∧: p2) (q1 :∨: q2)) True where
{- ConjLTop-}
instance {-# OVERLAPS #-} (AFRel (AFType p1 KTop) b1, AFRel (AFType p2 KTop) b2, (b1 || b2) ~ True)
         => AFRel (AFType (p1 :∧: p2) KTop) True where
{- ConjLProjC-}
instance {-# OVERLAPS #-} (AFRel (AFType p1 (C q)) b1, AFRel (AFType p2 (C q)) b2, (b1 || b2) ~ True)
         => AFRel (AFType (p1 :∧: p2) (C q)) True where
{- ConjLProjRC-}
instance AFRel (AFType (p1 :∧: p2) (C (p1 :∧: p2))) True where
{- ConjLProjI-}
instance {-# OVERLAPS #-} (AFRel (AFType p1 (I q)) b1, AFRel (AFType p2 (I q)) b2, (b1 || b2) ~ True)
         => AFRel (AFType (p1 :∧: p2) (I q)) True where
{- ConjLName-}
instance {-# OVERLAPS #-} (AFRel (AFType p1 (KName s)) b1, AFRel (AFType p2 (KName s)) b2, (b1 || b2) ~ True)
         => AFRel (AFType (p1 :∧: p2) (KName s)) True where
{- ConjRDisjL -}
instance {-# OVERLAPS #-} (AFRel (AFType p1 q1) True, AFRel (AFType p1 q2) True,
          AFRel (AFType p2 q1) True, AFRel (AFType p2 q2) True)
         => AFRel (AFType (p1 :∨: p2) (q1 :∧: q2)) True where
{- ConjR -}
instance {-# OVERLAPS #-} (AFRel (AFType p q1) True, AFRel (AFType p q2) True)
         => AFRel (AFType p (q1 :∧: q2) ) True where
{- ConjRBot -}
instance {-# OVERLAPS #-} (AFRel (AFType KBot q1) True, AFRel (AFType KBot q2) True)
         => AFRel (AFType KBot (q1 :∧: q2)) True where
{-TODO: Disj de-overlapping so that inference algorithm tries both DisjL and DisjR  -}
{- DisjL -}
instance {-# OVERLAPS #-} (AFRel (AFType p1 q) True, AFRel (AFType p2 q) True)
         => AFRel (AFType (p1 :∨: p2) q) True where
{- DisjR -}
instance {-# OVERLAPS #-} (AFRel (AFType p q1) b1, AFRel (AFType p q2) b2, (b1 || b2) ~ True)
          => AFRel (AFType p (q1 :∨: q2)) True where
{- Proj (C) -}
instance {-# OVERLAPS #-} AFRel (AFType p q) True => AFRel (AFType (C p) (C q)) True where
{- Proj (I) -}
instance {-# OVERLAPS #-} AFRel (AFType p q) True => AFRel (AFType (I p) (I q)) True where
{- ConjLReflL -}
instance {-# INCOHERENT #-} AFRel (AFType (p1 :∧: p2) p1) True where
{- ConjLReflR -}
instance {-# INCOHERENT #-} AFRel (AFType (p1 :∧: p2) p2) True where
{- ConjLBot-}
instance {-# INCOHERENT #-} AFRel (AFType (p1 :∧: p2) KBot) True where
{- ConjLProjRI-}
instance {-# INCOHERENT #-} AFRel (AFType (p1 :∧: p2) (I (p1 :∧: p2))) True where
{- ConjRTop -}
instance {-# INCOHERENT #-} AFRel (AFType KTop (q1 :∧: q2)) True where
{- Refl -}
--instance {-# INCOHERENT #-} AFRel (AFType p p) True
instance {-# INCOHERENT #-} AFRel (AFType KTop KTop) True where
instance {-# INCOHERENT #-} AFRel (AFType KBot KBot) True where
instance {-# INCOHERENT #-} AFRel (AFType (KName s) (KName s)) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: q) (p :∧: q)) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∨: q) (p :∨: q)) True where
instance {-# INCOHERENT #-} AFRel (AFType (C p) (C p)) True where
instance {-# INCOHERENT #-} AFRel (AFType (I p) (I p)) True where
{- Bot -}
instance {-# INCOHERENT #-} AFRel (AFType p KBot) True where
{- Top -}
instance {-# INCOHERENT #-} AFRel (AFType KTop q) True where
{- ProjR (C) -}
instance {-# INCOHERENT #-} AFRel (AFType p (C p)) True where
{- ProjR (I) -}
instance {-# INCOHERENT #-} AFRel (AFType p (I p)) True where
{- Equivalence relationships (see prinEq is Coq proof) -}
{- Lattice commutativity -}
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: q) (q :∧: p)) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∨: q) (q :∨: p)) True where
{- Lattice associativity (+ symmetry) -}
instance {-# INCOHERENT #-} AFRel (AFType ((p :∧: q) :∧: r) (p :∧: (q :∧: r))) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: (q :∧: r)) ((p :∧: q) :∧: r)) True where
instance {-# INCOHERENT #-} AFRel (AFType ((p :∨: q) :∨: r) (p :∨: (q :∨: r))) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∨: (q :∨: r)) ((p :∨: q) :∨: r)) True where
{- Lattice absorption (+ symmetry) -}
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: (p :∨: q)) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p (p :∧: (p :∨: q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∨: (p :∧: q)) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p (p :∨: (p :∧: q))) True where
{- Lattice idempotence (+ symmetry) -}
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: p) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p (p :∧: p)) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∨: p) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p (p :∨: p)) True where
{- Lattice identity (+ symmetry) -}
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: KBot) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p (p :∧: KBot)) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∨: KTop) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p (p :∨: KTop)) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: KTop) KTop) True where
instance {-# INCOHERENT #-} AFRel (AFType KTop (p :∧: KTop)) True where
instance {-# INCOHERENT #-} AFRel (AFType (p :∨: KBot) KBot) True where
instance {-# INCOHERENT #-} AFRel (AFType KBot (p :∨: KBot)) True where
{- Lattice distributivity (+ symmetry) -}
instance {-# INCOHERENT #-} AFRel (AFType (p :∧: (q :∨: r))
                       ((p :∧: q) :∨: (p :∧: r)))  True where
instance {-# INCOHERENT #-} AFRel (AFType ((p :∧: q) :∨: (p :∧: r))
                       (p :∧: (q :∨: r))) True where
{- Authority projections, property 3: distribution over conjunctions (+ symmetry) -}
instance {-# INCOHERENT #-} AFRel (AFType ((C p) :∧: (C q)) (C (p :∧: q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (C (p :∧: q)) ((C p) :∧: (C q))) True where
instance {-# INCOHERENT #-} AFRel (AFType ((I p) :∧: (I q)) (I (p :∧: q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (I (p :∧: q)) ((I p) :∧: (I q))) True where

{- Authority projections, property 4: distribution over disjunctions (+ symmetry) -}
instance {-# INCOHERENT #-} AFRel (AFType (C (p :∨: q)) ((C p) :∨: (C q))) True where
instance {-# INCOHERENT #-} AFRel (AFType ((C p) :∨: (C q)) (C (p :∨: q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (I (p :∨: q)) ((I p) :∨: (I q))) True where
instance {-# INCOHERENT #-} AFRel (AFType ((I p) :∨: (I q)) (I (p :∨: q))) True where
{- Authority projections, property 5: idempotence (+ symmetry)-}
instance {-# INCOHERENT #-} AFRel (AFType (C (C p)) (C p)) True where
instance {-# INCOHERENT #-} AFRel (AFType (C p) (C (C p))) True where
instance {-# INCOHERENT #-} AFRel (AFType (I (I p)) (I p)) True where
instance {-# INCOHERENT #-} AFRel (AFType (I p) (I (I p))) True where
{- Basis projections, properties 2-3 (+ symmetry)-}
instance {-# INCOHERENT #-} AFRel (AFType KBot (C (I p))) True where
instance {-# INCOHERENT #-} AFRel (AFType (I (C p)) KBot) True where
instance {-# INCOHERENT #-} AFRel (AFType KBot (I (C p))) True where
instance {-# INCOHERENT #-} AFRel (AFType ((C p) :∨: (I q)) KBot) True where
instance {-# INCOHERENT #-} AFRel (AFType KBot ((C p) :∨: (I q))) True where
-- Redundant, admissible instances to avoid necessity of transitive argument via KBot
instance {-# INCOHERENT #-} AFRel (AFType p (C (I q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (C (I p)) (C (I q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (I (C p)) (C (I q))) True where
instance {-# INCOHERENT #-} AFRel (AFType p (I (C q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (I (C p)) (I (C q))) True where
instance {-# INCOHERENT #-} AFRel (AFType (C (I p)) (I (C q))) True where
{- Admitted equivalences (+ symmetry)-}
instance {-# INCOHERENT #-} AFRel (AFType ((C p) :∧: (I p)) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p ((C p) :∧: (I p))) True where
instance {-# INCOHERENT #-} AFRel (AFType ((I p) :∧: (C p)) p) True where
instance {-# INCOHERENT #-} AFRel (AFType p ((I p) :∧: (C p))) True where
instance {-# INCOHERENT #-} AFRel (AFType (C KBot) KBot) True where
instance {-# INCOHERENT #-} AFRel (AFType KBot (C KBot)) True where
instance {-# INCOHERENT #-} AFRel (AFType (I KBot) KBot) True where
instance {-# INCOHERENT #-} AFRel (AFType KBot (I KBot)) True where

{- Exported actsfor relation -} 
class AFRel (AFType p q) True => ActsFor (p :: KPrin) (q :: KPrin) where
instance AFRel (AFType p q) True => ActsFor p q 

class EqRel (p :: KPrin) (q :: KPrin) where
instance (ActsFor p q, ActsFor q p) => EqRel p q where

{- Exported equivalence relation -} 
class EqRel p q => PrinEq (p :: KPrin) (q :: KPrin) where
instance EqRel p q => PrinEq p q 

--XXX: TODO: refactor FlowsTo
--type FlowsTo l l' = ActsFor ((C l') :∧: (I l)) ((C l) :∧: (I l'))

class FlowRel p q where
instance {-# INCOHERENT #-} (AFRel (AFType p (C cl)) b1,  AFRel (AFType q (C cl)) b2,  
                               ActsFor (I il) p,  ActsFor (I il) q,
                               (b1 || b2) ~ True) => FlowRel ((C cl) :∧: (I il)) (p :∧: q) where
instance {-# INCOHERENT #-} (ActsFor p (C cl), ActsFor (I il) p,  ActsFor (I il) (I ih))
                             => FlowRel ((C cl) :∧: (I il)) (p :∧: (I ih)) where
instance {-# INCOHERENT #-} (AFRel (AFType (C ch) (C cl)) b1,  AFRel (AFType q (C cl)) b2, ActsFor (I il) q,
                               (b1 || b2) ~ True) => FlowRel ((C cl) :∧: (I il)) ((C ch) :∧: q) where
instance {-# INCOHERENT #-} ActsFor ((C ch) :∧: (I il)) ((C cl) :∧: (I ih))
                                => FlowRel ((C cl) :∧: (I il)) ((C ch) :∧: (I ih)) where
instance {-# INCOHERENT #-} ActsFor (I p) q => FlowRel ((C p) :∧: (I p)) (p :∧: q) where
instance {-# INCOHERENT #-} ActsFor (I q) p => FlowRel ((C q) :∧: (I p)) (p :∧: q) where
instance {-# OVERLAPS #-} ActsFor (C ch) (C cl) => FlowRel (C cl) (C ch)
instance {-# OVERLAPS #-} ActsFor (I il) (I ih) => FlowRel (I il) (I ih)
instance {-# OVERLAPS #-} ActsFor (I il) (I ih) => FlowRel (I il) ((C ch) :∧: (I ih))
instance {-# OVERLAPS #-} ActsFor (C ch) (I cl) => FlowRel ((C cl) :∧: (I il)) (C ch)
{- Refl -}
instance {-# INCOHERENT #-} FlowRel p p
instance {-# INCOHERENT #-} FlowRel (C p) (C p)
instance {-# INCOHERENT #-} FlowRel (I p) (I p)
instance {-# INCOHERENT #-} FlowRel (KName s) (KName s)
instance {-# INCOHERENT #-} FlowRel ((C c) :∧: (I i)) ((C c) :∧: (I i)) where
instance {-# INCOHERENT #-} FlowRel ((C c) :∨: (I i)) ((C c) :∨: (I i)) where
{- Exported flow relation -} 
class FlowRel l l' => FlowsTo (l :: KPrin) (l' :: KPrin) where
instance FlowRel l l' => FlowsTo l l'
{-
-}

assertEq :: (PrinEq l l', PrinEq l' l) => SPrin l -> SPrin l' -> ()
assertEq l l' = ()

assertEqL :: (PrinEq l l') => SPrin l -> SPrin l' -> ()
assertEqL l l' = ()

assertEqR :: (PrinEq l' l) => SPrin l -> SPrin l' -> ()
assertEqR l l' = ()

--eqTSym :: PrinEq l' l => SPrin l -> SPrin l' -> ()
--eqTSym l l' = assertEq l l'

--eqTTrans :: (PrinEq p q, PrinEq q r) => SPrin p -> SPrin q -> SPrin r -> ()
--eqTTrans p q r = assertEqL p r

eqTConjComm :: SPrin p -> SPrin q -> ()
eqTConjComm p q = assertEq (p ∧ q) (q ∧ p) 

eqTDisjComm :: SPrin p -> SPrin q -> ()
eqTDisjComm p q = assertEq (p ∨ q) (q ∨ p) 

eqTConjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjAssoc p q r = assertEq ((p ∧ q) ∧ r) (p ∧ (q ∧ r))

eqTDisjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTDisjAssoc p q r = assertEq ((p ∨ q) ∨ r) (p ∨ (q ∨ r))

eqTDisjAbsorb :: SPrin p -> SPrin q -> ()
eqTDisjAbsorb p q = assertEq (p ∧ (p ∨ q)) p 
                    
eqTConjAbsorb :: SPrin p -> SPrin q -> ()
eqTConjAbsorb p q = assertEq (p ∨ (p ∧ q)) p 

eqTConjIdemp :: SPrin p -> ()
eqTConjIdemp p = assertEq (p ∧ p) p 

eqTDisjIdemp :: SPrin p -> ()
eqTDisjIdemp p = assertEq (p ∨ p) p 

eqTConjIdent :: SPrin p -> ()
eqTConjIdent p = assertEq (p ∧ pbot) p 
                 
eqTDisjIdent :: SPrin p -> ()
eqTDisjIdent p = assertEq (p ∨ ptop) p 

eqTConjTop :: SPrin p -> ()
eqTConjTop p = assertEq (p ∧ ptop) ptop 
       
eqTDisjBot :: SPrin p -> ()
eqTDisjBot p = assertEq (p ∨ pbot) pbot

eqTConjDistDisj :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjDistDisj p q r = assertEq (p ∧ (q ∨ r)) ((p ∧ q) ∨ (p ∧ r))

eqTConjConf :: SPrin p -> SPrin q -> ()
eqTConjConf p q = assertEq ((p ∧ q)^→) ((p^→) ∧ (q^→))

eqTConjInteg :: SPrin p -> SPrin q -> ()
eqTConjInteg p q = assertEq ((p ∧ q)^←) ((p^←) ∧ (q^←))

eqTDisjConf :: SPrin p -> SPrin q -> ()
eqTDisjConf p q = assertEq ((p ∨ q)^→) ((p^→) ∨ (q^→))

eqTDisjInteg :: SPrin p -> SPrin q -> ()
eqTDisjInteg p q = assertEq ((p ∨ q)^←) ((p^←) ∨ (q^←))

eqTConfIdemp :: SPrin p -> ()
eqTConfIdemp p = assertEq ((p^→)^→) (p^→)

eqTIntegIdemp :: SPrin p -> ()
eqTIntegIdemp p = assertEq ((p^←)^←) (p^←)

eqTConfInteg :: SPrin p -> ()
eqTConfInteg p = assertEq ((p^→)^←) pbot

eqTIntegConf :: SPrin p -> ()
eqTIntegConf p = assertEq ((p^←)^→) pbot

eqTConfDisjInteg :: SPrin p -> SPrin q -> ()
eqTConfDisjInteg p q = assertEq ((p^→) ∨ (q^←)) pbot

eqTConfIntegBasis :: SPrin p -> ()
eqTConfIntegBasis p = assertEq ((p^←) ∧ (p^→)) p

eqTBotConf :: ()
eqTBotConf = assertEq (pbot^→) pbot

eqTBotInteg :: ()
eqTBotInteg = assertEq (pbot^←) pbot
--
----eqTConjSubst :: (PrinEq p p', PrinEq q q') => 
----                  SPrin p -> SPrin p' -> SPrin q -> SPrin q' -> ()
----eqTConjSubst p p' q q' = assertEqL (p ∧ q) (p' ∧ q')
----
----eqTDisjSubst :: (PrinEq p p', PrinEq q q') => 
----                  SPrin p -> SPrin p' -> SPrin q -> SPrin q' -> ()
----eqTDisjSubst p p' q q' = assertEqL (p ∨ q) (p' ∨ q')
----
----eqTConfSubst :: PrinEq p p' => SPrin p -> SPrin p' -> ()
----eqTConfSubst p p' = assertEqL (p^→) (p'^→)
----
----eqTIntegSubst :: PrinEq p p' => SPrin p -> SPrin p' -> ()
----eqTIntegSubst p p' = assertEqL (p^←) (p'^←)
--                             
--
assertCBT0 :: ActsFor (I (C KBot)) (I (C KTop))  => ()
assertCBT0 = ()
testCBT0 = assertCBT0

assertCBT :: FlowsTo (C KBot) (C KTop) => ()
assertCBT = ()
testCBT = assertCBT

assertRCV :: SPrin p -> FlowsTo (KConj (C p) (I p)) (KConj p (I KBot)) => ()
assertRCV p = ()
testRCV = assertRCV

assertCBT2 :: (ActsFor (C (C KTop)) (C (C KBot)), ActsFor (I (C KBot)) (I (C KTop))) => ()
assertCBT2 = ()
testCBT2 = assertCBT2

assertITB :: FlowsTo (I KTop) (I KBot) => ()
assertITB = ()
testITB = assertITB

--neg_flTConf ::  SPrin p -> ()
--neg_flTConf p = assertFlowsTo ((p^→) ∧ (SBot^←)) p
--
-- XXX: TODO: current gets 'Overlapping instances' error
--neg_flTConf2 ::  SPrin p -> SPrin q -> ()
--neg_flTConf2 p q = assertActsFor SBot (SConf q) --(p^→) 
--
-- XXX: TODO: current gets 'Overlapping instances' error
--neg_flTInteg ::  SPrin p -> SPrin q -> ()
--neg_flTInteg p q = assertActsFor (p^→) ((p^→) ∧ (q^←))

flTConfConjL :: SPrin p ->  SPrin q -> ()
flTConfConjL p q = assertFlowsTo (p^→) ((p ∧ q)^→)  

assertActsFor :: ActsFor p q => SPrin p -> SPrin q -> ()
assertActsFor p q = ()
assertFlowsTo :: FlowsTo l l' => SPrin l -> SPrin l' -> ()
assertFlowsTo l l' = ()
{- A Flow-indexed monad for pure computations -}
class FIxMonad (m :: KPrin -> * -> *) where
  label   :: a -> m l a
  labelx  :: SPrin l -> a -> m l a
  lbind   :: FlowsTo l l' => m l a -> (a -> m l' b) -> m l' b
  unlabel :: FlowsTo l PT => m l a -> a

  (*>>=) :: FlowsTo l l' => m l a -> (a -> m l' b) -> m l' b
  (*>>=) = lbind

  relabel :: FlowsTo l l' => m l a -> m l' a
  relabel lx = lx *>>= (\x -> label x)

  relabelx :: FlowsTo l l' => SPrin l' -> m l a -> m l' a
  relabelx l' lx = lx *>>= (\x -> labelx l' x)

  fmapx  :: SPrin l -> (a -> b) -> m l a -> m l b
  fmapx l f x = x *>>= (\y -> labelx l (f y))

  ljoin  :: FlowsTo l l' => m l (m l' a) -> m l' a
  ljoin x = x *>>= id

{- A type for labeled computations -}
data Lbl (l::KPrin) a where
  MkLbl :: { unsafeRunLbl :: a } -> Lbl l a

instance FIxMonad Lbl where
  label       = MkLbl
  labelx l    = MkLbl 
  unlabel     = unsafeRunLbl
  lbind  m f  = f $ unsafeRunLbl m

instance Functor (Lbl l) where
  fmap f action = MkLbl $ f . unsafeRunLbl $ action  

instance Applicative (Lbl l) where
  pure     = MkLbl 
  a <*> b  = MkLbl $ (unsafeRunLbl a) $ (unsafeRunLbl b)

instance Monad (Lbl s) where
  return x = MkLbl x
  MkLbl a >>= k = k a

{- A type for lifting computations to IFCMonad -}
data IFC (pc::KPrin) (l::KPrin) a = UnsafeIFC { runIFC :: IO (Lbl l a) }

liftLbl :: Lbl l a -> IFC pc l a
liftLbl x = UnsafeIFC $ do return x

liftLblx :: SPrin pc -> Lbl l a -> IFC pc l a
liftLblx pc x = UnsafeIFC $ do return x

protect :: a -> IFC pc l a
protect x = UnsafeIFC $ do return (MkLbl x)

protectx :: SPrin pc -> SPrin l -> a -> IFC pc l a
protectx pc l x = UnsafeIFC $ do return (MkLbl x)

relabelIFC  :: (FlowsTo pc pc', FlowsTo l l')  => IFC pc l a -> IFC pc' l' a 
relabelIFC x = UnsafeIFC $ do a <- runIFC x;
                              --return . relabel a  -- this didn't work. why?
                              return $ MkLbl (unsafeRunLbl a)

relabelIFCx :: FlowsTo l l' => SPrin l -> SPrin l' -> IFC pc l a -> IFC pc l' a 
relabelIFCx l l' x = UnsafeIFC $ do
                              a <- runIFC x;
                              --return . relabel a  -- this didn't work. why?
                              return $ MkLbl (unsafeRunLbl a)

relabelIFCpc  :: (FlowsTo l l', FlowsTo pc pc') => SPrin pc' -> SPrin l' -> IFC pc l a -> IFC pc' l' a 
relabelIFCpc pc' l' x = UnsafeIFC $ do
                              a <- runIFC x;
                              return $ MkLbl (unsafeRunLbl a)

-- Something like this?
--withTrans :: (ActsFor p q, ActsFor q r) => SPrin p -> SPrin q -> SPrin r -> (ActsFor p r => a) -> a
--withTrans p q r a = using (DAFType p r) a  

{- Explicit relabeling rules -}
unsafeRelabel :: IFC pc l a -> IFC pc' l' a 
unsafeRelabel x = UnsafeIFC $ do
                                a <- runIFC x
                                return $ MkLbl (unsafeRunLbl a)
 
conjSubst :: (PrinEq p p', PrinEq q q') =>
             SPrin p' -> SPrin q' -> IFC pc (p :∧: q) a -> IFC pc (p' :∧: q') a 
conjSubst p' q' = unsafeRelabel

conjFlowL :: FlowsTo l l' =>
             SPrin l' -> SPrin q -> IFC pc (l :∧: q) a -> IFC pc (l' :∧: q) a 
conjFlowL l' q = unsafeRelabel -- TODO: this should not require unsafeRelabeling.

disjSubst :: (PrinEq p p', PrinEq q q') =>
             SPrin p' -> SPrin q' -> IFC pc (p :∨: q) a -> IFC pc (p' :∨: q') a 
disjSubst p' q' = unsafeRelabel

conjComm :: IFC pc (p :∧: q) a -> IFC pc (q :∧: p) a 
conjComm = unsafeRelabel

conjComm_pc :: IFC (p :∧: q) l a -> IFC (q :∧: p) l  a 
conjComm_pc  = unsafeRelabel

disjComm :: IFC pc (p :∨: q) a -> IFC pc (q :∨: p) a 
disjComm = unsafeRelabel

disjComm_pc :: IFC (p :∨: q) l a -> IFC (q :∨: p) l  a 
disjComm_pc  = unsafeRelabel

conjAssocR :: IFC pc ((p :∧: q) :∧: r) a -> IFC pc (p :∧: (q :∧: r)) a 
conjAssocR = unsafeRelabel

conjAssocR_pc :: IFC ((p :∧: q) :∧: r) l a -> IFC (p :∧: (q :∧: r)) l  a 
conjAssocR_pc  = unsafeRelabel

conjAssocL :: IFC pc (p :∧: (q :∧: r)) a -> IFC pc ((p :∧: q) :∧: r) a 
conjAssocL = unsafeRelabel

conjAssocL_pc' :: IFC (p :∧: (q :∧: r)) l a -> IFC ((p :∧: q) :∧: r) l  a 
conjAssocL_pc' = unsafeRelabel

disjAssoc :: IFC pc ((p :∨: q) :∨: r) a -> IFC pc (p :∨: (q :∨: r)) a 
disjAssoc = unsafeRelabel

disjAssoc_pc :: IFC ((p :∨: q) :∨: r) l a -> IFC (p :∨: (q :∨: r)) l  a 
disjAssoc_pc  = unsafeRelabel

{- Use a labeled value to perform effectful computation.
   Once side-effects are run, continue at arbitrary pc. -}
--use :: (FlowsTo l pc', FlowsTo l l')
--          => Lbl l a -> (a -> IFC pc' l' b) -> IFC pc l' b 
--use m f = UnsafeIFC $ do 
--                        result <- runIFC (f $ unsafeRunLbl m)
--                        return result

use :: (FlowsTo pc pc', FlowsTo l pc', FlowsTo l l')
          => IFC pc l a -> (a -> IFC pc' l' b) -> IFC pc l' b 
use m f = UnsafeIFC $ do 
                        v <- runIFC m
                        result <- runIFC (f $ unsafeRunLbl v)
                        return result

instance Functor (IFC pc l) where
-- SecIO leaves this undefined; is this safe or not?
--  fmap f action = error "fmap not secure since would permit arbitrary IO operations"
  fmap f action = UnsafeIFC $ do  
                                 result <- runIFC action  
                                 return $ MkLbl $ f $ unsafeRunLbl result

instance Applicative (IFC pc l) where
  pure     = UnsafeIFC . return . MkLbl 
-- SecIO leaves this undefined; is this safe or not?
--  a <*> b  = error "<*> not secure since would permit arbitrary IO operations"
  a <*> b  = UnsafeIFC $ do
                          f <- runIFC a
                          x <- runIFC b
                          return . MkLbl $ (unsafeRunLbl f) $ (unsafeRunLbl x)

instance Monad (IFC pc l) where
    return = UnsafeIFC . return . MkLbl
    (UnsafeIFC m) >>= k = UnsafeIFC $ do
                                        la <- m
                                        runIFC . k $ unsafeRunLbl la
--TODO: fix using stuff
{-
{- Machinery for dynamically extending the acts-for relation 
   From: https://www.schoolofhaskell.com/user/thoughtpolice/using-reflection -}
-- Should not be exported? 
data Lift (p :: * -> Constraint) (a :: *) (s :: *) = Lift { lower :: a }
-- Should not be exported? 
class ReifiableConstraint p where
  data Def (p :: * -> Constraint) (a :: *) :: *
  reifiedIns :: Reifies s (Def p a) :- p (Lift p a s)
 
-- added 'b' to allow more general computation qualified by constraint p
-- Should not be exported (directly).
using :: forall p a b. ReifiableConstraint p => Def p a -> (p a => b) -> b
using d m = reify d $ \(_ :: Proxy s) ->
  let replaceProof :: Reifies s (Def p a) :- p a
      replaceProof = trans proof reifiedIns
        where proof = unsafeCoerceConstraint :: p (Lift p a s) :- p a
  in m \\ replaceProof

instance ReifiableConstraint AFRel where
  data Def AFRel (AFType p q) = DAFType { sup_ :: SPrin p, inf_ :: SPrin q}
  reifiedIns = Sub Dict

{- Allow proofs to derive from dynamic relationships -}
instance Reifies s (Def AFRel a) => AFRel (Lift AFRel a s) where
 
type DAFType p q = Def AFRel (AFType p q)
-- TODO Voice + extra premises
assume :: --ActsFor pc (I q) => 
            DAFType p q -> (AFRel (AFType p q) => IFC pc l b) -> IFC pc l b 
assume pf m = using pf m 

assertAFRel :: AFRel (AFType p q) => SPrin p -> SPrin q -> () 
assertAFRel p q = ()

afTest :: ()
afTest = withPrin (Name "Alice") (\alice ->
           withPrin Top (\ptop ->
             withPrin Bot (\pbot ->
               using (DAFType (st alice) (st ptop)) $
                 using (DAFType (st pbot) (st ptop)) $
                   assertAFRel ((st alice) ∨ (st pbot)) (st ptop))))

afTest2 :: SPrin p -> SPrin q -> ()
afTest2 p q = using (DAFType (p^←) (q^←)) $ assertFlowsTo (p^←) (q^←)

afTest3 :: SPrin p -> SPrin q -> ()
afTest3 p q = using (DAFType (p^←) (q^←)) $ assertFlowsTo (p^←) ((p^←) ∧ (q^←))

afTest4 :: SPrin p -> SPrin q -> ()
afTest4 p q = let from = (p^→) in
              let to   = (p^→) ∧ (p^←) in
              using (DAFType ((p^→)) ((p^→) ∧ (p^←)))
                    (assertActsFor from to)
-}
--assertFlowRel :: FlowRel (FlowType p q) => SPrin p -> SPrin q -> () 
--assertFlowRel p q = ()
--
--flowTest :: ()
--flowTest = withPrin (Name "Alice") (\alice ->
--           withPrin Top (\ptop ->
--             withPrin Bot (\pbot ->
--               using (DFlowType (st alice) (st ptop)) $
--                 using (DFlowType (st pbot) (st ptop)) $
--                   assertFlowRel ((st pbot)) (st ptop))))

{- Bind runtime principal to type -}
withPrin :: Prin -> (forall p . Bound p -> a) -> a
withPrin p f = case promote p of
                 Ex p' -> f (p <=> p') 
