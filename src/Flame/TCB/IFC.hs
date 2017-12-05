{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.TCB.IFC where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection
import Data.Functor.Identity 

import Flame.Principals
import Flame.TCB.Assume

data Label (c :: * -> Constraint) (l::KPrin) a where
  Return :: c a => a -> Label c l a
  Bind   :: (c a, l ⊑ l') => Label c l a -> (a -> Label c l' b) -> Label c l' b

lbl_runLabel :: Label c l a -> Label c l a
lbl_runLabel (Return v)   = Return v
lbl_runLabel (Bind lv f) = let (Return v) = lbl_runLabel lv in (f v)


lbl_unsafeUnlabel :: Label c l a  -> a
lbl_unsafeUnlabel (Return v) = v
lbl_unsafeUnlabel (Bind lv f) = let v = lbl_unsafeUnlabel lv in
                                  lbl_unsafeUnlabel (f v)

testAdd :: Lbl l Int -> Lbl l Int -> Int
testAdd a b = unsafeUnlabel $ bind a $ \a' -> 
                              bind b $ \b' -> label (a' + b')

class Labeled (c :: * -> Constraint) (n :: (* -> Constraint) -> KPrin -> * -> *) where
  label         :: c a => a -> n c l a
  bind          :: (c a, c b, l ⊑ l') => n c l a -> (a -> n c l' b) -> n c l' b
  unsafeUnlabel :: c a => n c l a -> a
  relabel       :: (c a, l ⊑ l') => n c l a -> n c l' a
  relabel a = bind a label 

instance Labeled c Label where
  label         = Return
  bind          = Bind
  unsafeUnlabel = lbl_unsafeUnlabel

class CTrue a where {}
instance CTrue a where {}

type Lbl l a = Label CTrue l a

data FLAC (c :: * -> Constraint) e (n :: (* -> Constraint) -> KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  Lift          :: (c a, Monad e) => n c l a -> FLAC c e n pc l a
  EBind         :: (c a, c b, Monad e, l ⊑ l', l ⊑ pc') => n c l a -> (a -> FLAC c e n pc' l' b) -> FLAC c e n pc l' b
  Apply         :: (c a, c b, Monad e, pc ⊑ pc', pc ⊑ pc'') => FLAC c e n pc l a -> (n c l a -> FLAC c e n pc' l' b) -> FLAC c e n pc'' l' b
  Join          :: (c a, l ⊑ l',  pc ⊑ pc', l ⊑ pc') => FLAC c e n pc l (FLAC c e n pc' l' a) -> FLAC c e n pc' l' a
  UnsafeProtect :: (c a, Monad e) => e (n c l a) -> FLAC c e n pc l a

{-
--runCFLAC :: CFLAC c e n pc l a -> e (n c l a)
--runCFLAC (CLift lv) = UnsafeFLAC $ Prelude.return x

{- Information flow control based on FLAM acts-for constraints -}
class (Monad e, CLabeled c n) => CIFC (c :: * -> Constraint) (m :: (* -> Constraint) -> (* -> *) -> ((* -> Constraint) -> KPrin -> * -> *) -> KPrin -> KPrin -> * -> *) e n where
  clift   :: (c a, pc ⊑ l) => n c l a -> m c e n pc l a

  capply  :: (c a, c b, pc ⊑ pc', pc ⊑ pc'') => m c e n pc l a -> (n c l a -> m c e n pc' l' b) -> m c e n pc'' l' b

  cebind  :: (c a, c b, l ⊑ l', l ⊑ pc) => n c l a -> (a -> m c e n pc l' b) -> m c e n pc' l' b

  cunsafeProtect :: c a => e (n c l a) -> m c e n pc l a


  cprotect :: (c a, pc ⊑ l) => a -> m c e n pc l a
  cprotect = clift . clabel

  cuse :: forall l l' pc pc' pc'' a b. (c a, c b, l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'') =>
         m c e n pc l a -> (a -> m c e n pc' l' b) -> m c e n pc'' l' b
  cuse x f = capply x $ \x' -> (cebind x' f :: m c e n pc' l' b)
 
  creprotect :: forall l l' pc pc' a. (c a, l ⊑ l', pc ⊑ pc', (pc ⊔ l) ⊑ l') => m c e n pc l a -> m c e n pc' l' a 
  creprotect x = cuse x (cprotect :: a -> m c e n (pc ⊔ l) l' a)

  cffmap :: forall l l' pc pc' a b. (c a, c b, l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l') => (a -> b) -> m c e n pc l a -> m c e n pc' l' b
  cffmap f x = cuse x (\x' -> cprotect (f x') :: m c e n (pc ⊔ l) l' b)

  cfjoin  :: forall l l' pc pc' a. (c a, l ⊑ l',  pc ⊑ pc', l ⊑ pc') => m c e n pc l (m c e n pc' l' a) -> m c e n pc' l' a

instance Monad e => CIFC c CFLAC e CLbl where
  clift  = CLift
  cebind = CEBind
  capply = CApply
  cunsafeProtect = CUnsafeProtect
--  crunIFC  = runCFLAC
  cfjoin = CJoin
-}






-- instance CIFC c m e n pc l a => RunnableIFC c m e n pc l a
--   crunIFC :: c a => m c e n pc l a -> e (n c l a)
-- 
-- instance CIFC c m e n pc l a => CompiledIFC c m e n pc l a
--   compileIFC :: c a => m c e n pc l a -> e (n c l a)
{-
{- An indexed monad for information flow on pure computation -}
class Labeled (n :: KPrin -> * -> *) where
  label     :: a -> n l a
  bind      :: (l ⊑ l') => n l a -> (a -> n l' b) -> n l' b
  unlabelPT :: n PT a -> a
  unlabelU  :: n l () -> ()
  unsafeUnlabel :: n l a -> a
  
  relabel :: (l ⊑ l') => n l a -> n l' a
  relabel a = bind a label

{- Information flow control based on FLAM acts-for constraints -}
class (Monad e, Labeled n) => IFC (m :: (* -> *) -> (KPrin -> * -> *) -> KPrin -> KPrin -> * -> *) e n where
  lift   :: (pc ⊑ l) => n l a -> m e n pc l a

  apply  :: (pc ⊑ pc', pc ⊑ pc'') => m e n pc l a -> (n l a -> m e n pc' l' b) -> m e n pc'' l' b

  ebind  :: (l ⊑ l', l ⊑ pc) => n l a -> (a -> m e n pc l' b) -> m e n pc' l' b

  unsafeProtect :: e (n l a) -> m e n pc l a

  runIFC :: m e n pc l a -> e (n l a)

  protect :: (pc ⊑ l) => a -> m e n pc l a
  protect = lift . label

  use :: forall l l' pc pc' pc'' a b. (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'') =>
         m e n pc l a -> (a -> m e n pc' l' b) -> m e n pc'' l' b
  use x f = apply x $ \x' -> (ebind x' f :: m e n pc' l' b)
 
  reprotect :: forall l l' pc pc' a. (l ⊑ l', pc ⊑ pc', (pc ⊔ l) ⊑ l') => m e n pc l a -> m e n pc' l' a 
  reprotect x = use x (protect :: a -> m e n (pc ⊔ l) l' a)

  ffmap :: forall l l' pc pc' a b. (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l') => (a -> b) -> m e n pc l a -> m e n pc' l' b
  ffmap f x = use x (\x' -> protect (f x') :: m e n (pc ⊔ l) l' b)

  fjoin  :: forall l l' pc pc' a. (l ⊑ l',  pc ⊑ pc', l ⊑ pc') => m e n pc l (m e n pc' l' a) -> m e n pc' l' a
  fjoin x = use x id

{- Flow-limited authorization for IFC types -}
class IFC m e n => FLA m e n where
  assume :: (pc ≽ ((I q) ∧ (∇) q), (∇) p ≽ (∇) q) =>
              (p :≽ q) -> ((p ≽ q) => m e n pc l a) -> m e n pc l a
  assume = unsafeAssume
  assume2 :: (pc ≽ ((I q) ∧ (∇) q)) =>
              (p :≽ q) -> ((p ≽ q, (∇) p ≽ (∇) q) => m e n pc l a) -> m e n pc l a
  assume2 (Del p q) f = unsafeAssume ((*∇) p ≽ (*∇) q) $ unsafeAssume (p ≽ q) f


{- Nonmalleable information flow control -}
class IFC m e n => NMIF m e n where
  declassify :: (((C pc) ⊓ (C l')) ⊑ (C l)
                 , (C pc) ⊑ (C l')
                 , (C l') ⊑ ((C l) ⊔ (Δ (I l' ⊔ I pc)))
                 , (I l') === (I l)) =>
             m e n pc l' a -> m e n pc l a 
  declassify x = unsafeProtect $ do
    x' <- runIFC x 
    return $ label (unsafeUnlabel x')
  endorse    :: ( ((I pc) ⊓ (I l')) ⊑ (I l)
                , (I pc) ⊑ (I l')
                , (I l') ⊑ ((I l) ⊔ ((∇) (C l' ⊔ C pc)))
                --, (I l') ⊑ ((I l) ⊔ ((∇) (C l')))
                --, (I l') ⊑ ((I l) ⊔ ((∇) (C pc)))
                , (C l') === (C l)
                ) =>
             m e n pc l' a -> m e n pc l a 
  endorse x = unsafeProtect $ do
    x' <- runIFC x 
    return $ label (unsafeUnlabel x')
{- A type for pure labeled computations -}
data Lbl (l::KPrin) a where
  UnsafeMkLbl :: { unsafeRunLbl :: a } -> Lbl l a
-- both the constructor and destructor must be private:
--   since either will unlabel a value
--   (the constructor enables pattern matching)

lbl_label :: a -> Lbl l a
lbl_label = UnsafeMkLbl

lbl_bind :: (l ⊑ l') => Lbl l a -> (a -> Lbl l' b) -> Lbl l' b    
lbl_bind x f = f (unsafeRunLbl x)

lbl_unlabelPT :: Lbl PT a -> a
lbl_unlabelPT a = unsafeRunLbl a

lbl_unlabelU :: Lbl l () -> ()
lbl_unlabelU a = unsafeRunLbl a

{- A Labeled instance for Lbl -}
instance Labeled Lbl where
  label = lbl_label
  bind  = lbl_bind
  unsafeUnlabel = unsafeRunLbl
  unlabelPT = lbl_unlabelPT 
  unlabelU = lbl_unlabelU


{- A transformer for effectful labeled computations -}
data FLACT e (n :: KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  UnsafeFLAC :: { runFLAC :: e (n l a) } -> FLACT e n pc l a

{- FLAC computations -}
type FLAC e pc l a = FLACT e Lbl pc l a

flac_lift :: Monad e => Lbl l a -> FLAC e pc l a
flac_lift  x = UnsafeFLAC $ Prelude.return x

flac_ebind :: (Monad e, l ⊑ l', l ⊑ pc') => Lbl l a -> (a -> FLAC e pc' l' b) -> FLAC e pc l' b
flac_ebind x f = UnsafeFLAC $ runFLAC $ f $ unsafeRunLbl x

flac_apply :: (Monad e, pc ⊑ pc', pc ⊑ pc'') => FLAC e pc l a -> (Lbl l a -> FLAC e pc' l' b) -> FLAC e pc'' l' b
flac_apply x f = UnsafeFLAC $ do
                   a <- runFLAC x
                   runFLAC $ f a

instance Monad e => IFC FLACT e Lbl where
  lift    = flac_lift 
  ebind   = flac_ebind
  apply   = flac_apply
  unsafeProtect = UnsafeFLAC
  runIFC  = runFLAC

instance Monad e => FLA FLACT e Lbl where {}

{- A transformer for effectful labeled computations -}
data NMT e (n :: KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  UnsafeNM :: { runNM :: e (n l a) } -> NMT e n pc l a

type NM e pc l a = NMT e Lbl pc l a

nmif_lift :: Monad e => Lbl l a -> NM e pc l a
nmif_lift  x = UnsafeNM $ Prelude.return x

nmif_ebind :: (Monad e, l ⊑ l', l ⊑ pc') => Lbl l a -> (a -> NM e pc' l' b) -> NM e pc l' b
nmif_ebind x f = UnsafeNM $ runNM $ f $ unsafeRunLbl x

nmif_apply :: (Monad e, pc ⊑ pc', pc ⊑ pc'') => NM e pc l a -> (Lbl l a -> NM e pc' l' b) -> NM e pc'' l' b
nmif_apply x f = UnsafeNM $ do
                   a <- runNM x
                   runNM $ f a

instance Monad e => IFC NMT e Lbl where
  lift    = nmif_lift 
  ebind   = nmif_ebind
  apply   = nmif_apply
  unsafeProtect = UnsafeNM
  runIFC  = runNM

instance Monad e => NMIF NMT e Lbl where {}
{-
-}
-}