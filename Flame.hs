{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances, IncoherentInstances #-}

{-# LANGUAGE Rank2Types, FlexibleContexts, UndecidableInstances, TypeFamilies #-}
{-# LANGUAGE ConstraintKinds, KindSignatures, PolyKinds, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}

module Flame
       (Prin(..) , DPrin(..)
       , C, I
       , PT, Public, Trusted
       , public, trusted, publicTrusted
       , IFC, runIFC
       , protect
       , Lbl
       , label
       , unlabel
       , flaReadFile
       , flaRun
       , IFCController, IFCApplication
       )
  where

import GHC.TypeLits
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Data.Proxy (Proxy(..))
import Control.Monad
import Control.Monad.IO.Class
import Data.Type.Set

import Network.Wai 
import Network.Wai.Handler.Warp

import qualified Data.ByteString as S

import Web.Simple.Controller.Trans

type IFCApplication (pc::Prin) (l::Prin) = Request
                      -> (Response -> IFC pc l ResponseReceived)
                      -> IFC pc l ResponseReceived
type IFCController (pc::Prin) (l::Prin) s = ControllerT s (IFC pc l)

-- TODO: move network stuff to Flame.Simple and Flame.Network.Wai
-- TODO: move IO stuff to 

data Prin =
  Top
  | Bot
  | Name Symbol 
  | Conj Prin Prin 
  | Disj Prin Prin
  | Conf Prin
  | Integ Prin

{- Singleton GADT for Prin -}
data DPrin :: Prin -> * where
  DTop   :: DPrin Top
  DBot   :: DPrin Bot
  DName  :: forall (n :: Symbol). Proxy n -> DPrin (Name n)
  DConj  :: DPrin p -> DPrin q -> DPrin (Conj p q)
  DDisj  :: DPrin p -> DPrin q -> DPrin (Disj p q)
  DConf  :: DPrin p -> DPrin (Conf p)
  DInteg :: DPrin p -> DPrin (Integ p)

{- Wrapped principals -}
data Ex (p ::k -> *) where
  Ex :: p i -> Ex p

type WPrin = Ex DPrin

wrapPrin :: Prin -> WPrin
wrapPrin Top           = Ex DTop
wrapPrin Bot           = Ex DBot
wrapPrin (Name s)      = Ex (DName (Proxy :: Proxy s))
wrapPrin (Conj p q)    = case wrapPrin p of
                          Ex p' -> case wrapPrin q of
                                     Ex q' -> Ex (DConj p' q')
wrapPrin (Disj p q)    = case wrapPrin p of
                          Ex p' -> case wrapPrin q of
                                     Ex q' -> Ex (DDisj p' q')
wrapPrin (Conf p)      = case wrapPrin p of Ex p' -> Ex (DConf p')
wrapPrin (Integ p)     = case wrapPrin p of Ex p' -> Ex (DConf p')

{- Some notation help -}
type C p = Conf p
type I p = Integ p
type p :/\: q = Conj p q
type p :∧: q  = Conj p q
type p :\/: q = Disj p q
type p :∨: q  = Disj p q
type p :⊔: q  = ((C p) :∧: (C q)) :∧: ((I p) :∨: (I q))
type p :⊓: q  = ((C p) :∨: (C q)) :∧: ((I p) :∧: (I q))
type Public  = Conf Bot
type Trusted = Integ Top
type PT      = Public :∧: Trusted 

(^->) p = DConf p
(^→)  p = DConf p
(^<-) p = DInteg p
(^←)  p = DInteg p
(/\) p q = DConj p q
(∧)  p q = DConj p q

(\/) p q = DDisj p q
(∨)  p q = DDisj p q
(⊔)  p q  = ((p^→) ∧ (q^→)) ∧ ((p^←) ∨ (q^←))
(⊓)  p q  = ((p^→) ∨ (q^→)) ∧ ((p^←) ∧ (q^←))

ptop = DTop
pbot = DBot
public  = DConf pbot
trusted = DInteg ptop
publicTrusted = public ∧ trusted           

data AFType (p :: Prin) (q :: Prin) = AFType { sup :: DPrin p, inf :: DPrin q}

{- Type class for the FLAC static acts-for relation, including 
   relationships deriving from principal equivalence. -}
class AFRel del where
{- Bot -}
instance                                               AFRel (AFType p Bot) where
{- Top -}
instance                                               AFRel (AFType Top q) where
{- Refl -}
instance                                               AFRel (AFType p p) where
{- ConjL -}
instance AFRel (AFType p1 q) =>                        AFRel (AFType (Conj p1 p2) q) where
{- ConjR -}
instance (AFRel (AFType p q1), AFRel (AFType p q2)) => AFRel (AFType p (Conj q1 q2)) where
{- DisjL -}
instance (AFRel (AFType p1 q), AFRel (AFType p2 q)) => AFRel (AFType (Disj p1 p2) q) where
{- DisjR -}
instance AFRel (AFType p q1) =>                        AFRel (AFType p (Disj q1 q2)) where
{- Proj (Conf) -}
instance AFRel (AFType p q) =>                         AFRel (AFType (Conf p) (Conf q))
{- Proj (Integ) -}
instance AFRel (AFType p q) =>                         AFRel (AFType (Integ p) (Integ q))
{- ProjR (Conf) -}
instance                                               AFRel (AFType p (Conf q)) 
{- ProjR (Integ) -}
instance                                               AFRel (AFType p (Integ q)) 
{- Trans -}
instance (AFRel (AFType p q) , AFRel (AFType q r)) =>  AFRel (AFType p r) where
{- Equivalence relationships (see prinEq is Coq proof) -}
{- Lattice commutativity -}
instance                               AFRel (AFType (Conj p q) (Conj q p)) where
instance                               AFRel (AFType (Disj p q) (Disj q p)) where
{- Lattice associativity (+ symmetry) -}
instance                               AFRel (AFType (Conj (Conj p q) r) (Conj p (Conj q r))) where
instance                               AFRel (AFType (Conj p (Conj q r)) (Conj (Conj p q) r)) where
instance                               AFRel (AFType (Disj (Disj p q) r) (Disj p (Disj q r))) where
instance                               AFRel (AFType (Disj p (Disj q r)) (Disj (Disj p q) r)) where
{- Lattice absorption (+ symmetry) -}
instance                               AFRel (AFType (Conj p (Disj p q)) p) where
instance                               AFRel (AFType p (Conj p (Disj p q))) where
instance                               AFRel (AFType (Disj p (Conj p q)) p) where
instance                               AFRel (AFType p (Disj p (Conj p q))) where
{- Lattice idempotence (+ symmetry) -}
instance                               AFRel (AFType (Conj p p) p) where
instance                               AFRel (AFType p (Conj p p)) where
instance                               AFRel (AFType (Disj p p) p) where
instance                               AFRel (AFType p (Disj p p)) where
{- Lattice identity (+ symmetry) -}
instance                               AFRel (AFType (Conj p Bot) p) where
instance                               AFRel (AFType p (Conj p Bot)) where
instance                               AFRel (AFType (Disj p Top) p) where
instance                               AFRel (AFType p (Disj p Top)) where
instance                               AFRel (AFType (Conj p Top) Top) where
instance                               AFRel (AFType Top (Conj p Top)) where
instance                               AFRel (AFType (Disj p Bot) Bot) where
instance                               AFRel (AFType Bot (Disj p Bot)) where
{- Lattice distributivity (+ symmetry) -}
instance                               AFRel (AFType (Conj p (Disj q r))
                                                       (Disj (Conj p q) (Conj p j)) )  where
instance                               AFRel (AFType (Disj (Conj p q) (Conj p j))
                                                       (Conj p (Disj q r))) where
{- Authority projections, property 3: distribution over conjunctions (+ symmetry) -}
instance                               AFRel (AFType (Conj (Conf p) (Conf q)) (Conf (Conj p q)) ) where
instance                               AFRel (AFType (Conf (Conj p q)) (Conj (Conf p) (Conf q))  ) where
instance                               AFRel (AFType (Conj (Integ p) (Integ q)) (Integ (Conj p q)) ) where
instance                               AFRel (AFType (Integ (Conj p q)) (Conj (Integ p) (Integ q))  ) where

{- Authority projections, property 4: distribution over disjunctions (+ symmetry) -}
instance                               AFRel (AFType (Conf (Disj p q)) (Disj (Conf p) (Conf q)) ) where
instance                               AFRel (AFType (Disj (Conf p) (Conf q)) (Conf (Disj p q)) ) where
instance                               AFRel (AFType (Integ (Disj p q)) (Disj (Integ p) (Integ q)) ) where
instance                               AFRel (AFType (Disj (Integ p) (Integ q)) (Integ (Disj p q)) ) where
{- Authority projections, property 5: idempotence (+ symmetry)-}
instance                               AFRel (AFType (Conf (Conf p)) (Conf p) ) where
instance                               AFRel (AFType (Conf p) (Conf (Conf p)) ) where
instance                               AFRel (AFType (Integ (Integ p)) (Integ p) ) where
instance                               AFRel (AFType (Integ p) (Integ (Integ p)) ) where
{- Basis projections, properties 2-3 (+ symmetry)-}
instance                               AFRel (AFType Bot (Conf (Integ p)) ) where
--instance                               AFRel (AFType (Integ (Conf p)) Bot ) where
instance                               AFRel (AFType Bot (Integ (Conf p)) ) where
--instance                               AFRel (AFType (Disj (Conf p) (Integ q)) Bot ) where
instance                               AFRel (AFType Bot (Disj (Conf p) (Integ q)) ) where
-- Why does the solver need help on these equivalences to bottom? b/c transitivity?
instance                               AFRel (AFType (Conf (Integ p)) (Conf (Integ q)) ) where
instance                               AFRel (AFType (Integ (Conf p)) (Integ (Conf q)) ) where
instance                               AFRel (AFType (Conf (Integ p)) (Integ (Conf p)) ) where
instance                               AFRel (AFType (Integ (Conf p)) (Conf (Integ q)) ) where
{- Admitted equivalences (+ symmetry)-}
instance                               AFRel (AFType (Conj (Conf p) (Integ p)) p ) where
instance                               AFRel (AFType p (Conj (Conf p) (Integ p)) ) where
instance                               AFRel (AFType (Conj (Integ p) (Conf p)) p ) where
instance                               AFRel (AFType p (Conj (Integ p) (Conf p)) ) where
instance                               AFRel (AFType (Conf Bot) Bot ) where
instance                               AFRel (AFType Bot (Conf Bot) ) where
instance                               AFRel (AFType (Integ Bot) Bot ) where
instance                               AFRel (AFType Bot (Integ Bot) ) where
-- what does this mean? what it should mean?
instance (n1 ~ n2)   =>                AFRel (AFType (Name n1) (Name n2) ) where

 
class ActsFor (p :: Prin) (q :: Prin) where
instance AFRel (AFType p q) => ActsFor p q where

class PrinEq (p :: Prin) (q :: Prin) where
instance (ActsFor p q, ActsFor q p) => PrinEq p q where
{- Substitutions (no symmetry!) -}
--instance (PrinEq p p', PrinEq q q') => PrinEq (Conj p q) (Conj p' q') where
--instance (PrinEq p p', PrinEq q q') => PrinEq (Disj p q) (Disj p' q') where
--instance PrinEq p p' =>                PrinEq (Conf p) (Conf p') where
--instance PrinEq p p' =>                PrinEq (Integ p) (Integ p') where

class FlowsTo (l :: Prin) (l' :: Prin) where
instance ActsFor p q => FlowsTo (Conj (Conf q) (Integ p)) (Conj (Conf p) (Integ q))  where
instance ActsFor (Conf l') (Conf l) => FlowsTo (Conf l) (Conf l')
instance ActsFor (Integ l') (Integ l) => FlowsTo (Integ l') (Integ l)
instance (ActsFor (Conf l') (Conf l), ActsFor (Integ l) (Integ l')) => FlowsTo l l'

assertEq :: (PrinEq l l', PrinEq l' l) => DPrin l -> DPrin l' -> ()
assertEq l l' = ()

assertEqL :: (PrinEq l l') => DPrin l -> DPrin l' -> ()
assertEqL l l' = ()

assertEqR :: (PrinEq l' l) => DPrin l -> DPrin l' -> ()
assertEqR l l' = ()

eqTRefl :: DPrin l -> ()
eqTRefl l = assertEq l l

--eqTSym :: PrinEq l' l => DPrin l -> DPrin l' -> ()
--eqTSym l l' = assertEq l l'

--eqTTrans :: (PrinEq p q, PrinEq q r) => DPrin p -> DPrin q -> DPrin r -> ()
--eqTTrans p q r = assertEqL p r

eqTConjComm :: DPrin p -> DPrin q -> ()
eqTConjComm p q = assertEq (p ∧ q) (q ∧ p) 

eqTDisjComm :: DPrin p -> DPrin q -> ()
eqTDisjComm p q = assertEq (p ∨ q) (q ∨ p) 

eqTConjAssoc :: DPrin p -> DPrin q -> DPrin r -> ()
eqTConjAssoc p q r = assertEq ((p ∧ q) ∧ r) (p ∧ (q ∧ r))

eqTDisjAssoc :: DPrin p -> DPrin q -> DPrin r -> ()
eqTDisjAssoc p q r = assertEq ((p ∨ q) ∨ r) (p ∨ (q ∨ r))

eqTDisjAbsorb :: DPrin p -> DPrin q -> ()
eqTDisjAbsorb p q = assertEq (p ∧ (p ∨ q)) p 
                    
eqTConjAbsorb :: DPrin p -> DPrin q -> ()
eqTConjAbsorb p q = assertEq (p ∨ (p ∧ q)) p 

eqTConjIdemp :: DPrin p -> ()
eqTConjIdemp p = assertEq (p ∧ p) p 

eqTDisjIdemp :: DPrin p -> ()
eqTDisjIdemp p = assertEq (p ∨ p) p 

eqTConjIdent :: DPrin p -> ()
eqTConjIdent p = assertEq (p ∧ pbot) p 
                 
eqTDisjIdent :: DPrin p -> ()
eqTDisjIdent p = assertEq (p ∨ ptop) p 

eqTConjTop :: DPrin p -> ()
eqTConjTop p = assertEq (p ∧ ptop) ptop 
       
eqTDisjBot :: DPrin p -> ()
eqTDisjBot p = assertEq (p ∨ pbot) pbot

eqTConjDistDisj :: DPrin p -> DPrin q -> DPrin r -> ()
eqTConjDistDisj p q r = assertEq (p ∧ (q ∨ r)) ((p ∧ q) ∨ (p ∧ r))

eqTConjConf :: DPrin p -> DPrin q -> ()
eqTConjConf p q = assertEq ((p ∧ q)^→) ((p^→) ∧ (q^→))

eqTConjInteg :: DPrin p -> DPrin q -> ()
eqTConjInteg p q = assertEq ((p ∧ q)^←) ((p^←) ∧ (q^←))

eqTDisjConf :: DPrin p -> DPrin q -> ()
eqTDisjConf p q = assertEq ((p ∨ q)^→) ((p^→) ∨ (q^→))

eqTDisjInteg :: DPrin p -> DPrin q -> ()
eqTDisjInteg p q = assertEq ((p ∨ q)^←) ((p^←) ∨ (q^←))

eqTConfIdemp :: DPrin p -> ()
eqTConfIdemp p = assertEq ((p^→)^→) (p^→)

eqTIntegIdemp :: DPrin p -> ()
eqTIntegIdemp p = assertEq ((p^←)^←) (p^←)

eqTConfInteg :: DPrin p -> ()
eqTConfInteg p = assertEq ((p^→)^←) pbot

eqTIntegConf :: DPrin p -> ()
eqTIntegConf p = assertEq ((p^←)^→) pbot

eqTConfDisjInteg :: DPrin p -> DPrin q -> ()
eqTConfDisjInteg p q = assertEq ((p^→) ∨ (q^←)) pbot

eqTConfIntegBasis :: DPrin p -> ()
eqTConfIntegBasis p = assertEq ((p^←) ∧ (p^→)) p

eqTBotConf :: ()
eqTBotConf = assertEq (pbot^→) pbot

eqTBotInteg :: ()
eqTBotInteg = assertEq (pbot^←) pbot

--eqTConjSubst :: (PrinEq p p', PrinEq q q') => 
--                  DPrin p -> DPrin p' -> DPrin q -> DPrin q' -> ()
--eqTConjSubst p p' q q' = assertEqL (p ∧ q) (p' ∧ q')

--eqTDisjSubst :: (PrinEq p p', PrinEq q q') => 
--                  DPrin p -> DPrin p' -> DPrin q -> DPrin q' -> ()
--eqTDisjSubst p p' q q' = assertEqL (p ∨ q) (p' ∨ q')
--
--eqTConfSubst :: PrinEq p p' => DPrin p -> DPrin p' -> ()
--eqTConfSubst p p' = assertEqL (p^→) (p'^→)
--
--eqTIntegSubst :: PrinEq p p' => DPrin p -> DPrin p' -> ()
--eqTIntegSubst p p' = assertEqL (p^←) (p'^←)
                               

assertCBT0 :: ActsFor (I (C Bot)) (I (C Top))  => ()
assertCBT0 = ()
testCBT0 = assertCBT0

assertCBT :: FlowsTo (C Bot) (C Top) => ()
assertCBT = ()
testCBT = assertCBT

assertCBT2 :: (ActsFor (C (C Top)) (C (C Bot)), ActsFor (I (C Bot)) (I (C Top))) => ()
assertCBT2 = ()
testCBT2 = assertCBT2

assertITB :: FlowsTo (I Top) (I Bot) => ()
assertITB = ()
testITB = assertITB

assertActsFor :: ActsFor p q => DPrin p -> DPrin q -> ()
assertActsFor p q = ()

assertFlowsTo :: FlowsTo l l' => DPrin l -> DPrin l' -> ()
assertFlowsTo l l' = ()

--neg_flTconfName ::  DPrin p -> ()
--neg_flTconfName p = checkFlowsTo ((p^→) ∧ (bot^←)) p

flTConjL :: DPrin p ->  DPrin q -> ()
flTConjL p q = assertFlowsTo (p^→) ((p ∧ q)^→)  

{- A Flow-indexed monad for pure computations -}
class FIxMonad (m :: Prin -> * -> *) where
  label   :: a -> m l a
  labelx  :: DPrin l -> a -> m l a
  lbind   :: FlowsTo l l' => m l a -> (a -> m l' b) -> m l' b
  unlabel :: FlowsTo l PT => m l a -> a

  (*>>=) :: FlowsTo l l' => m l a -> (a -> m l' b) -> m l' b
  (*>>=) = lbind

  relabel :: FlowsTo l l' => m l a -> m l' a
  relabel lx = lx *>>= (\x -> label x)

  relabelx :: FlowsTo l l' => DPrin l' -> m l a -> m l' a
  relabelx l' lx = lx *>>= (\x -> labelx l' x)

  fmapx  :: DPrin l -> (a -> b) -> m l a -> m l b
  fmapx l f x = x *>>= (\y -> labelx l (f y))

  ljoin  :: FlowsTo l l' => m l (m l' a) -> m l' a
  ljoin x = x *>>= id

{- A type for labeled computations -}
data Lbl l a where
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

testC :: Lbl (C Bot) a -> Lbl (C Top) a
testC x = x *>>= (\y -> label y)

testI :: Lbl (I Top) a -> Lbl (I Bot) a
testI x = x *>>= (\y -> label y)

testCI :: Lbl ((C Bot) :∧: (I Top)) a -> Lbl ((C Top) :∧: (I Bot)) a
testCI x = x *>>= (\y -> label y)

testToBasis :: Lbl p a -> Lbl ((C p) :∧: (I p)) a                                                                
testToBasis x = x *>>= (\y -> label y)
 
testFromBasis :: Lbl ((C p) :∧: (I p)) a -> Lbl p a
testFromBasis x = x *>>= (\y -> label y)

--TODO: implement fail

{- A type for lifting computations to IFCMonad -}
data IFC pc l a = UnsafeIFC { runIFC :: IO (Lbl l a) }

liftLbl :: Lbl l a -> IFC pc l a
liftLbl x = UnsafeIFC $ do return x

liftLblx :: DPrin pc -> Lbl l a -> IFC pc l a
liftLblx pc x = UnsafeIFC $ do return x

protect :: a -> IFC pc l a
protect x = UnsafeIFC $ do return (MkLbl x)

protectx :: DPrin pc -> DPrin l -> a -> IFC pc l a
protectx pc l x = UnsafeIFC $ do return (MkLbl x)

relabelIFC  :: (FlowsTo pc pc', FlowsTo l l')  => IFC pc l a -> IFC pc' l' a 
relabelIFC x = UnsafeIFC $ do a <- runIFC x;
                              --return . relabel a  -- this didn't work. why?
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
  data Def AFRel (AFType p q) = DAFType { sup_ :: DPrin p, inf_ :: DPrin q}
  reifiedIns = Sub Dict

instance Reifies s (Def AFRel a) => AFRel (Lift AFRel a s) where

assertAFRel :: AFRel (AFType p q) => DPrin p -> DPrin q -> () 
assertAFRel p q = ()

type DAFType p q = Def AFRel (AFType p q)
dynAF :: DPrin p -> DPrin q -> DAFType p q
dynAF p q = DAFType p q

afTest :: ()
afTest = using (dynAF alice ptop) $ using (dynAF pbot ptop) $ assertAFRel (alice ∨ pbot) ptop

-- TODO Voice
assume :: (ActsFor pc (Integ q), ActsFor l (Integ q)) => IFC pc l (DAFType p q) -> (AFRel (AFType p q) => IFC pc' l' b) -> IFC pc' l' b 
assume lpf m = UnsafeIFC $ do
                  pf <- runIFC lpf  
                  runIFC $ using (unsafeRunLbl pf) m 

flaPutStrLn :: (FlowsTo l lblout, FlowsTo pc lblout) => IFC pc l String -> IFC lblout l' ()
flaPutStrLn str = UnsafeIFC $ do
                               s <- runIFC str 
                               u <- putStrLn $ unsafeRunLbl s 
                               return (MkLbl u)

{- Dynamically check whether file has label fileLbl -}
checkFileLbl :: DPrin fileLbl -> FilePath -> Bool
-- TODO: implement
checkFileLbl lbl fp = True

flaReadFile :: DPrin fileLbl -> FilePath -> IFC pc fileLbl (Either String S.ByteString)
flaReadFile lbl fp = UnsafeIFC $ if checkFileLbl lbl fp
                                  then do 
                                    u <- S.readFile fp
                                    return (MkLbl (Right u))
                                  else 
                                    return (MkLbl (Left "Access check failed"))

unsafeUnlabelApp :: IFCApplication pc l -> Application
unsafeUnlabelApp app req responseFunc = do 
            resp <- runIFC (app req (UnsafeIFC . (\resp -> do
                                                             r <- responseFunc resp
                                                             return (MkLbl r))))
            return $ unsafeRunLbl $ resp
  
flaRun :: DPrin pc -> DPrin l -> Port -> IFCApplication pc l -> IFC pc l () 
flaRun pc l port app = UnsafeIFC $ do
                                     run port (unsafeUnlabelApp app);
                                     return (MkLbl ())

type Alice = (Name "Alice")           
alice :: DPrin (Name "Alice")
alice = DName (Proxy :: Proxy "Alice")
type Bob   = (Name "Bob")           
type Carol = (Name "Carol")           
type Terminal = (Name "Terminal")           
tName :: DPrin (Name "Terminal")
tName = DName (Proxy :: Proxy "Terminal")

--TODO: check that (C (Alice :∨: Terminal)) flows to (C Terminal)
msgToAlice :: IFC (C Alice) (C Alice) String -> IFC (C Alice) l () 
msgToAlice msg = --let m = (relabelx (tName^→) (tName^→) msg) in
                     flaPutStrLn $ do
                                    s <- msg;
                                    return (s ++ " Alice")
testImplicit :: IFC (I Top) (C Alice) Bool -> IFC (C Top) l ()
testImplicit b = flaPutStrLn $ do 
                                tf <- b
                                return (if tf then "True" else "False")

sayHi :: IO ()
sayHi = putStrLn "Hello"
--main  :: IO (Lbl l ())
--main  =  runIFC $ testImplicit (protect False)
