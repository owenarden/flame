{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE IncoherentInstances #-}

{-# LANGUAGE Rank2Types, FlexibleContexts, UndecidableInstances, TypeFamilies #-}
{-# LANGUAGE ConstraintKinds, KindSignatures, PolyKinds, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
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

data Bound p = UnsafeBindP { dyn :: Prin, st :: SPrin p } 
dynamic = dyn
static = st 
-- do not export <=>. This ensures only using* code can associate runtime principals wth singleton principal types.
(<=>) :: Prin -> SPrin p -> Bound p
p <=> sp = UnsafeBindP p sp

data AFType (p :: KPrin) (q :: KPrin) = AFType { sup :: SPrin p, inf :: SPrin q}

data FlowType (l :: KPrin) (l' :: KPrin) = FlowType { finf :: SPrin l, fsup :: SPrin l'}

{- Type class for the FLAC static acts-for relation, including 
   relationships deriving from principal equivalence. -}
class AFRel del where
{- Bot -}
instance                              AFRel (AFType p KBot) where
{- Top -}
instance                              AFRel (AFType KTop q) where
{- Refl -}
instance                              AFRel (AFType p p) where
{- ConjL -}
instance  AFRel (AFType p1 q) =>                        AFRel (AFType (p1 :∧: p2) q) where
{- ConjR -}
instance  (AFRel (AFType p q1), AFRel (AFType p q2)) => AFRel (AFType p (q1 :∧: q2)) where
{- DisjL -}
instance  (AFRel (AFType p1 q), AFRel (AFType p2 q)) => AFRel (AFType (p1 :∨: p2) q) where
{- DisjR -}
instance  AFRel (AFType p q1) =>                        AFRel (AFType p (q1 :∨: q2)) where
{- Proj (C) -}
instance  AFRel (AFType p q) =>                         AFRel (AFType (C p) (C q))
{- Proj (I) -}
instance  AFRel (AFType p q) =>                         AFRel (AFType (I p) (I q))
{- ProjR (C) -}
instance                                                AFRel (AFType p (C p)) 
{- ProjR (I) -}
instance                                               AFRel (AFType p (I p)) 
{- Trans -}
instance (AFRel (AFType p q) , AFRel (AFType q r)) =>  AFRel (AFType p r) where
{- Equivalence relationships (see prinEq is Coq proof) -}
{- Lattice commutativity -}
instance               AFRel (AFType (p :∧: q) (q :∧: p)) where
instance               AFRel (AFType (p :∨: q) (q :∨: p)) where
{- Lattice associativity (+ symmetry) -}
instance               AFRel (AFType ((p :∧: q) :∧: r) (p :∧: (q :∧: r))) where
instance               AFRel (AFType (p :∧: (q :∧: r)) ((p :∧: q) :∧: r)) where
instance               AFRel (AFType ((p :∨: q) :∨: r) (p :∨: (q :∨: r))) where
instance               AFRel (AFType (p :∨: (q :∨: r)) ((p :∨: q) :∨: r)) where
{- Lattice absorption (+ symmetry) -}
instance                              AFRel (AFType (p :∧: (p :∨: q)) p) where
instance                              AFRel (AFType p (p :∧: (p :∨: q))) where
instance                              AFRel (AFType (p :∨: (p :∧: q)) p) where
instance                              AFRel (AFType p (p :∨: (p :∧: q))) where
{- Lattice idempotence (+ symmetry) -}
instance                              AFRel (AFType (p :∧: p) p) where
instance                              AFRel (AFType p (p :∧: p)) where
instance                              AFRel (AFType (p :∨: p) p) where
instance                              AFRel (AFType p (p :∨: p)) where
{- Lattice identity (+ symmetry) -}
instance                              AFRel (AFType (p :∧: KBot) p) where
instance                              AFRel (AFType p (p :∧: KBot)) where
instance                              AFRel (AFType (p :∨: KTop) p) where
instance                              AFRel (AFType p (p :∨: KTop)) where
instance                              AFRel (AFType (p :∧: KTop) KTop) where
instance                              AFRel (AFType KTop (p :∧: KTop)) where
instance                              AFRel (AFType (p :∨: KBot) KBot) where
instance                              AFRel (AFType KBot (p :∨: KBot)) where
{- Lattice distributivity (+ symmetry) -}
instance                              AFRel (AFType (p :∧: (q :∨: r))
                                                       ((p :∧: q) :∨: (p :∧: r)))  where
instance                              AFRel (AFType ((p :∧: q) :∨: (p :∧: r))
                                                       (p :∧: (q :∨: r))) where
{- Authority projections, property 3: distribution over conjunctions (+ symmetry) -}
instance                              AFRel (AFType ((C p) :∧: (C q)) (C (p :∧: q))) where
instance                              AFRel (AFType (C (p :∧: q)) ((C p) :∧: (C q))) where
instance                              AFRel (AFType ((I p) :∧: (I q)) (I (p :∧: q))) where
instance                              AFRel (AFType (I (p :∧: q)) ((I p) :∧: (I q))) where

{- Authority projections, property 4: distribution over disjunctions (+ symmetry) -}
instance                              AFRel (AFType (C (p :∨: q)) ((C p) :∨: (C q))) where
instance                              AFRel (AFType ((C p) :∨: (C q)) (C (p :∨: q))) where
instance                              AFRel (AFType (I (p :∨: q)) ((I p) :∨: (I q))) where
instance                              AFRel (AFType ((I p) :∨: (I q)) (I (p :∨: q))) where
{- Authority projections, property 5: idempotence (+ symmetry)-}
instance                              AFRel (AFType (C (C p)) (C p)) where
instance                              AFRel (AFType (C p) (C (C p))) where
instance                              AFRel (AFType (I (I p)) (I p)) where
instance                              AFRel (AFType (I p) (I (I p))) where
{- Basis projections, properties 2-3 (+ symmetry)-}
instance                              AFRel (AFType KBot (C (I p))) where
instance                              AFRel (AFType (I (C p)) KBot ) where
instance                              AFRel (AFType KBot (I (C p))) where
instance                              AFRel (AFType ((C p) :∨: (I q)) KBot ) where
instance                              AFRel (AFType KBot ((C p) :∨: (I q))) where
-- Why does the solver need help on these equivalences to bottom? b/c transitivity?
instance                              AFRel (AFType (C (I p)) (C (I q))) where
instance                              AFRel (AFType (I (C p)) (I (C q))) where
--instance                              AFRel (AFType (C p) (I q)) where
--instance                              AFRel (AFType (I p) (C q)) where
{- Admitted equivalences (+ symmetry)-}
instance                              AFRel (AFType ((C p) :∧: (I p)) p) where
instance                              AFRel (AFType p ((C p) :∧: (I p))) where
instance                              AFRel (AFType ((I p) :∧: (C p)) p) where
instance                              AFRel (AFType p ((I p) :∧: (C p))) where
instance                              AFRel (AFType (C KBot) KBot) where
instance                              AFRel (AFType KBot (C KBot)) where
instance                              AFRel (AFType (I KBot) KBot) where
instance                              AFRel (AFType KBot (I KBot)) where
-- Necessary?
--instance   (n1 ~ n2)   =>             AFRel (AFType (KName n1) (KName n2)) where

{- Exported actsfor relation -} 
class AFRel (AFType p q) => ActsFor (p :: KPrin) (q :: KPrin) where
instance AFRel (AFType p q) => ActsFor p q where

class EqRel (p :: KPrin) (q :: KPrin) where
instance (ActsFor p q, ActsFor q p) => EqRel p q where
{- Substitutions (no symmetry!) -}
--instance (PrinEq p p', PrinEq q q') => PrinEq (Conj p q) (Conj p' q') where
--instance (PrinEq p p', PrinEq q q') => PrinEq (Disj p q) (Disj p' q') where
--instance PrinEq p p' =>                PrinEq (Conf p) (Conf p') where
--instance PrinEq p p' =>                PrinEq (Integ p) (Integ p') where


{- Exported equivalence relation -} 
class EqRel p q => PrinEq (p :: KPrin) (q :: KPrin) where
instance EqRel p q => PrinEq p q

class FlowRel del  where
instance ActsFor p q => FlowRel (FlowType ((C q) :∧: (I p)) ((C p) :∧: (I q)))  where
instance (ActsFor (C l') (C l), ActsFor (I l) (I l')) => FlowRel (FlowType l l')
-- some redundant cases to help out the inference algorithm.
instance (ActsFor (C l'c) (C lc), ActsFor (I li) (I l'i)) => FlowRel (FlowType ((C lc) :∧: (I li)) ((C l'c) :∧: (I l'i)))
--instance ActsFor (C l') (C l) =>         FlowRel (FlowType (C l) (C l'))
--instance ActsFor (I l') (I l) =>         FlowRel (FlowType (I l') (I l))
--instance                                 FlowRel (FlowType (C KBot) (C l))
--instance                                 FlowRel (FlowType (I KTop) l)
--instance                                 FlowRel (FlowType l (C KTop))

{- Exported flow relation -} 
class FlowRel (FlowType l l') => FlowsTo (l :: KPrin) (l' :: KPrin) where
instance FlowRel (FlowType l l') => FlowsTo l l'

assertEq :: (PrinEq l l', PrinEq l' l) => SPrin l -> SPrin l' -> ()
assertEq l l' = ()

assertEqL :: (PrinEq l l') => SPrin l -> SPrin l' -> ()
assertEqL l l' = ()

assertEqR :: (PrinEq l' l) => SPrin l -> SPrin l' -> ()
assertEqR l l' = ()

eqTRefl :: SPrin l -> ()
eqTRefl l = assertEq l l

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

--eqTConjSubst :: (PrinEq p p', PrinEq q q') => 
--                  SPrin p -> SPrin p' -> SPrin q -> SPrin q' -> ()
--eqTConjSubst p p' q q' = assertEqL (p ∧ q) (p' ∧ q')
--
--eqTDisjSubst :: (PrinEq p p', PrinEq q q') => 
--                  SPrin p -> SPrin p' -> SPrin q -> SPrin q' -> ()
--eqTDisjSubst p p' q q' = assertEqL (p ∨ q) (p' ∨ q')
--
--eqTConfSubst :: PrinEq p p' => SPrin p -> SPrin p' -> ()
--eqTConfSubst p p' = assertEqL (p^→) (p'^→)
--
--eqTIntegSubst :: PrinEq p p' => SPrin p -> SPrin p' -> ()
--eqTIntegSubst p p' = assertEqL (p^←) (p'^←)
                             

assertCBT0 :: ActsFor (I (C KBot)) (I (C KTop))  => ()
assertCBT0 = ()
testCBT0 = assertCBT0

assertCBT :: FlowsTo (C KBot) (C KTop) => ()
assertCBT = ()
testCBT = assertCBT

assertCBT2 :: (ActsFor (C (C KTop)) (C (C KBot)), ActsFor (I (C KBot)) (I (C KTop))) => ()
assertCBT2 = ()
testCBT2 = assertCBT2

assertITB :: FlowsTo (I KTop) (I KBot) => ()
assertITB = ()
testITB = assertITB

assertActsFor :: ActsFor p q => SPrin p -> SPrin q -> ()
assertActsFor p q = ()
--
assertFlowsTo :: FlowsTo l l' => SPrin l -> SPrin l' -> ()
assertFlowsTo l l' = ()

--neg_flTConf ::  SPrin p -> ()
--neg_flTConf p = assertFlowsTo ((p^→) ∧ (SBot^←)) p

--neg_flTConf2 ::  SPrin p -> SPrin q -> ()
--neg_flTConf2 p q = assertActsFor SBot (SConf q) --(p^→) 

--neg_flTInteg ::  SPrin p -> SPrin q -> ()
--neg_flTInteg p q = assertActsFor (p^→) ((p^→) ∧ (q^←))

--flTConjL :: SPrin p ->  SPrin q -> ()
--flTConjL p q = assertFlowsTo (p^→) ((p ∧ q)^→)  

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

--testC :: Lbl (C KBot) a -> Lbl (C KTop) a
--testC x = x *>>= (\y -> label y)
--
--testI :: Lbl (I KTop) a -> Lbl (I KBot) a
--testI x = x *>>= (\y -> label y)
--
--testCI :: Lbl ((C KBot) :∧: (I KTop)) a -> Lbl ((C KTop) :∧: (I KBot)) a
--testCI x = x *>>= (\y -> label y)
--
--testToBasis :: Lbl p a -> Lbl ((C p) :∧: (I p)) a                                                                
--testToBasis x = x *>>= (\y -> label y)
-- 
--testFromBasis :: Lbl ((C p) :∧: (I p)) a -> Lbl p a
--testFromBasis x = x *>>= (\y -> label y)

--TODO: implement fail

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

relabelIFCpc  :: FlowsTo pc pc' => SPrin pc -> SPrin pc' -> IFC pc l a -> IFC pc' l a 
relabelIFCpc pc pc' x = UnsafeIFC $ do
                              a <- runIFC x;
                              return $ MkLbl (unsafeRunLbl a)

{- Use a labeled value to perform effectful computation.
   Once side-effects are run, continue at arbitrary pc. -}
use :: (FlowsTo l pc', FlowsTo l l')
          => Lbl l a -> (a -> IFC pc' l' b) -> IFC pc l' b 
use m f = UnsafeIFC $ do 
                        result <- runIFC (f $ unsafeRunLbl m)
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

instance Reifies s (Def AFRel a) => AFRel (Lift AFRel a s) where

type DAFType p q = Def AFRel (AFType p q)

instance ReifiableConstraint FlowRel where
  data Def FlowRel (FlowType l l') = DFlowType { finf_ :: SPrin l, fsup_ :: SPrin l'}
  reifiedIns = Sub Dict

instance Reifies s (Def FlowRel a) => FlowRel (Lift FlowRel a s) where

type DFlowType p q = Def FlowRel (FlowType p q)

assertAFRel :: AFRel (AFType p q) => SPrin p -> SPrin q -> () 
assertAFRel p q = ()

afTest :: ()
afTest = withPrin (Name "Alice") (\alice ->
           withPrin Top (\ptop ->
             withPrin Bot (\pbot ->
               using (DAFType (st alice) (st ptop)) $
                 using (DAFType (st pbot) (st ptop)) $
                   assertAFRel ((st alice) ∨ (st pbot)) (st ptop))))

assertFlowRel :: FlowRel (FlowType p q) => SPrin p -> SPrin q -> () 
assertFlowRel p q = ()

flowTest :: ()
flowTest = withPrin (Name "Alice") (\alice ->
           withPrin Top (\ptop ->
             withPrin Bot (\pbot ->
               using (DFlowType (st alice) (st ptop)) $
                 using (DFlowType (st pbot) (st ptop)) $
                   assertFlowRel ((st pbot)) (st ptop))))

-- TODO Voice + extra premises
assume :: (ActsFor pc (I q), ActsFor l (I q), ActsFor (I l) (I l'), ActsFor (C l) (C l')) => 
            IFC pc l (DAFType p q) -> (AFRel (AFType p q) => IFC pc' l' b) -> IFC pc' l' b 
assume lpf m = UnsafeIFC $ do
                  pf <- runIFC lpf  
                  runIFC $ using (unsafeRunLbl pf) m 

-- TODO Voice + extra premises
fassume :: (FlowsTo (I to) pc, FlowsTo (I to) l, FlowsTo l l') => 
            IFC pc l (DFlowType from to) -> (FlowRel (FlowType from to) => IFC pc l' b) -> IFC pc l' b 
fassume lpf m = UnsafeIFC $ do
                  pf <- runIFC lpf  
                  runIFC $ using (unsafeRunLbl pf) m 

{- Bind runtime principal to type -}
withPrin :: Prin -> (forall p . Bound p -> a) -> a
withPrin p f = case promote p of
                 Ex p' -> f (p <=> p') 

         
--type Alice = (KName "Alice")           
--type Bob   = (KName "Bob")           
--type Carol = (KName "Carol")           
--type Terminal = (KName "Terminal")           
--alice :: SPrin Alice
--alice = SName (Proxy :: Proxy "Alice")
--tName :: SPrin Terminal
--tName = SName (Proxy :: Proxy "Terminal")
--
--TODO: check that (C (Alice :∨: Terminal)) flows to (C Terminal)
--msgToAlice :: IFC (C Alice) (C Alice) String -> IFC (C Alice) l () 
--msgToAlice msg = --let m = (relabelx (tName^→) (tName^→) msg) in
--                     flaPutStrLn $ do
--                                    s <- msg;
--                                    return (s ++ " Alice")
--testImplicit :: IFC (I KTop) (C Alice) Bool -> IFC (C KTop) l ()
--testImplicit b = flaPutStrLn $ do 
--                                tf <- b
--                                return (if tf then "True" else "False")

--sayHi :: IO ()
--sayHi = putStrLn "Hello"
--main  :: IO ()
--main  = sayHi --putStrLn uIfTest2

--[Scratch]
--withDel :: IFC pc l Prin -> IFC pc l Prin -> (forall p q. IFC pc l (DAFType p q) -> IFC pc' l' a) -> IFC pc' l' a 
--withDel p_ q_ f = UnsafeIFC $ do
--                                lp <- runIFC p_
--                                lq <- runIFC q_
--                                runIFC $ let p = (unsafeRunLbl lp) in
--                                         let q = (unsafeRunLbl lq) in
--                                         case promote p of
--                                           Ex p' -> case promote q of
--                                                      Ex q' -> f $ protect $ DAFType (p <=> p') (q <=> q')
--
--withDelL :: IFC pc l Prin -> IFC pc l (Bound q) -> (forall p . IFC pc l (DAFType p q) -> IFC pc' l' a) -> IFC pc' l' a
--withDelL p_ q_ f = UnsafeIFC $ do
--                                lp <- runIFC p_
--                                lq <- runIFC q_
--                                runIFC $ let p = (unsafeRunLbl lp) in
--                                         let q = (unsafeRunLbl lq) in
--                                         case promote p of
--                                           Ex p' -> f $ protect $ DAFType (p <=> p') q
--     
--withDelR :: IFC pc l (Bound p) -> IFC pc l Prin -> (forall q . IFC pc l (DAFType p q) -> IFC pc' l' a) -> IFC pc' l' a
--withDelR p_ q_ f = UnsafeIFC $ do
--                                lp <- runIFC p_
--                                lq <- runIFC q_
--                                runIFC $ let p = (unsafeRunLbl lp) in
--                                         let q = (unsafeRunLbl lq) in
--                                         case promote q of
--                                           Ex q' -> f $ protect $ DAFType p (q <=> q')
--
--withDelB :: IFC pc l (Bound p) -> IFC pc l (Bound q) -> (IFC pc l (DAFType p q) -> IFC pc' l' a) -> IFC pc' l' a
--withDelB p_ q_ f = UnsafeIFC $ do
--                                lp <- runIFC p_
--                                lq <- runIFC q_
--                                runIFC ( let p = (unsafeRunLbl lp) in
--                                         let q = (unsafeRunLbl lq) in
--                                         f $ protect $ DAFType p q )
--

--afTest2 :: IFC pc l ()
--afTest2 = withDel (Name "Alice") Top (\(DAFType alice ptop) ->
--                                        assume (protectx ((st ptop)^←) ((st ptop)^←) (DAFType alice ptop))
--                                               (withDelL Bot ptop (\(DAFType pbot ptop2) ->
--                                                                     assume (protectx ((st ptop)^←) ((st ptop)^←) (DAFType pbot ptop))
--                                                                            (protect (assertAFRel ((st alice) ∨ (st pbot)) (st ptop))))))
--
--type Authorizer = Prin -> Prin -> Bool
--
--usingIf :: Authorizer -> Prin -> Prin -> (forall p q. Bound p -> Bound q -> AFRel (AFType p q) =>  b) -> b -> b
--usingIf auth p q ifTrue ifFalse = if auth p q then
--                               case promote p of
--                                 Ex p' -> case promote q of
--                                            Ex q' -> 
--                                              using (DAFType (p <=> p') (q <=> q')) $ ifTrue (p <=> p') (q <=> q')
--                             else 
--                               ifFalse
--
--usingIfR :: Authorizer -> Prin -> Bound q -> (forall p. Bound p -> AFRel (AFType p q) =>  b) -> b -> b
--usingIfR auth p q ifTrue ifFalse = if auth p (dyn q) then
--                                case promote p of
--                                  Ex p' -> using (DAFType (p <=> p') q) $ ifTrue (p <=> p')
--                              else 
--                                ifFalse
--
--usingIfL :: Authorizer -> Bound p -> Prin -> (forall q. Bound q -> AFRel (AFType p q) =>  b) -> b -> b
--usingIfL auth p q ifTrue ifFalse = if auth (dyn p) q then
--                                case promote q of
--                                  Ex q' -> using (DAFType p (q <=> q')) $ ifTrue (q <=> q')
--                              else 
--                                ifFalse
--
--usingIfB :: Authorizer -> Bound p -> Bound q -> (AFRel (AFType p q) =>  b) -> b -> b
--usingIfB auth p q ifTrue ifFalse = if auth (dyn p) (dyn q) then
--                                using (DAFType p q) ifTrue
--                              else 
--                                ifFalse
--dumbAF :: Authorizer
--dumbAF p q =
--  case p of
--     Bot -> True
--     (Name s) -> True
--     _ -> False
--
--uIfTest :: String 
--uIfTest = usingIf dumbAF Bot Top
--            (\b t -> let _ = assertAFRel (st b) (st t) in "Bot actsfor Top")
--            "DynBot does not actfor top"
--            
--
--uIfTest2 :: String 
--uIfTest2 = usingIf dumbAF (Name "Alice") (Name "Charlie")
--           (\a c -> let ig1 = assertAFRel (st a) (st c) in
--             usingIfR dumbAF (Name "Bob") c
--             (\b ->
--               let ig2 = assertAFRel ((st a) ∨ (st b)) (st c) in "OK")
--             "DynBot does not actfor top")
--           "Alice does not actsfor top"
--
--type FLAuthorizer pc l = IFC pc l Prin -> IFC pc l Prin -> IFC pc l Bool
--
--assumeIf :: 
--         FLAuthorizer pc l -> IFC pc l Prin -> IFC pc l Prin
--         -> (forall p q . Bound p -> Bound q -> AFRel (AFType p q) => IFC pc' l' b)
--         -> IFC pc' l' b
--         -> IFC pc' l' b
--assumeIf = undefined




        
