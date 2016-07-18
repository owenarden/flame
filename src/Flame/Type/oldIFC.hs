{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.IFC
       (
        FIxMonad (..), Lbl, IFC, runIFC,
        liftLbl, liftLblx,
        protect, protectx,
        relabel, relabelx, relabelxx,
        assume
       )
  where

import Flame.Type.Principals
 
{- A Flow-indexed monad for pure computations -}
class FIxMonad (m :: KPrin -> * -> *) where
  label   :: a -> m l a
  labelx  :: SPrin l -> a -> m l a
  lbind   :: (l ⊑ l') => m l a -> (a -> m l' b) -> m l' b
  unlabel :: (l ⊑ PT) => m l a -> a

  (*>>=) :: (l ⊑ l') => m l a -> (a -> m l' b) -> m l' b
  (*>>=) = lbind

  fmapx  :: SPrin l -> (a -> b) -> m l a -> m l b
  fmapx l f x = x *>>= (\y -> labelx l (f y))

  ljoin  :: (l ⊑ l') => m l (m l' a) -> m l' a
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

relabel  :: (pc ⊑ pc', l ⊑ l')  => IFC pc l a -> IFC pc' l' a 
relabel x = UnsafeIFC $ do a <- runIFC x;
                           --return . relabel a  -- this didn't work. why?
                           return $ MkLbl (unsafeRunLbl a)

relabelx :: (l ⊑ l') => SPrin l -> SPrin l' -> IFC pc l a -> IFC pc l' a 
relabelx l l' x = UnsafeIFC $ do
                           a <- runIFC x;
                           --return . relabel a  -- this didn't work. why?
                           return $ MkLbl (unsafeRunLbl a)

relabelxx  :: (pc ⊑ pc', l ⊑ l') => SPrin pc' -> SPrin l' -> IFC pc l a -> IFC pc' l' a 
relabelxx pc' l' x = UnsafeIFC $ do
                              a <- runIFC x;
                              return $ MkLbl (unsafeRunLbl a)

assume :: (pc ≽ Voice q, Voice (C p) ≽ Voice (C q)) =>
            (p :≽ q) -> ((p ≽ q) => IFC pc l a) -> IFC pc l a
assume pf m = unsafeAssume pf m
