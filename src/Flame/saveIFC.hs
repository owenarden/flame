{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.IFC
--       (
--        FLAMonad (..), Lbl, IFC,
--        runFLA,
--        liftLbl,
--        protect,
--        relabel,
--        assume
--       )
  where

import Flame.Principals
 
{- A type for labeled computations -}
data Lbl (l::KPrin) a where
  MkLbl :: { unsafeRunLbl :: a } -> Lbl l a

{- A type for lifting computations to IFCMonad -}
data Ctl (pc::KPrin) n (l::KPrin) a = UnsafeIFC { runIFC :: IO (n l a) }

type IFC pc l a = Ctl pc Lbl l a

{- A Flow-indexed monad for pure computations -}
class FLAMonad (m :: KPrin -> * -> *) (n :: KPrin -> * -> *) where
  label :: a -> n l a
  protect :: a -> m pc (n l a)

  fapply :: (pc ⊑ pc') => m pc (n l a) -> (n l a -> m pc' (n l' b)) -> m pc' (n l' b) 
  fbind :: (l ⊑ l', l ⊑ pc) => n l a -> (a -> m pc (n l' b)) -> m pc (n l' b)
  use :: (l ⊑ l', pc ⊑ pc', l ⊑ pc') => m pc (n l a) -> (a -> m pc' (n l' b)) -> m pc' (n l' b)
  use x f = fapply x $ \x' -> fbind x' f
  assume :: (pc ≽ Voice q, Voice (C p) ≽ Voice (C q)) =>
            (p :≽ q) -> ((p ≽ q) => m pc (n l a)) -> m pc (n l a)

  (*>>=) ::  (l ⊑ l', pc ⊑ pc', l ⊑ pc') => m pc (n l a) -> (a -> m pc' (n l' b)) -> m pc' (n l' b)
  (*>>=) = use

  ffmap :: (l ⊑ l', pc ⊑ pc', l ⊑ pc') => (a -> b) -> m pc (n l a) -> m pc' (n l' b)
  ffmap f x = x *>>= (\y -> protect (f y))

  fjoin  :: (l ⊑ l', pc ⊑ pc', l ⊑ pc') => m pc (n l (m pc' (n l' a))) -> m pc' (n l' a)
  fjoin x = x *>>= id

{-
instance FLAMonad IFC where
  label       = MkLbl
  labelx l    = MkLbl 
  unlabel     = unsafeRunLbl
  lbind  m f  = f $ unsafeRunLbl m

instance Functor (Lbl l) where
  fmap f action = MkLbl $ f . unsafeRunLbl $ action  

instance Applicative (Lbl l) where
  pure     = MkLbl 
  a <*> b  = MkLbl $ (unsafeRunLbl a) $ (unsafeRunLbl b)

instance Monad (Lbl l) where
  return x = MkLbl x
  MkLbl a >>= k = k a

lift :: Lbl l a -> IFC pc l a
lift x = UnsafeIFC $ do return x

--liftLblx :: SPrin pc -> Lbl l a -> IFC pc l a
--liftLblx pc x = UnsafeIFC $ do return x

protect :: a -> IFC pc l a
protect x = UnsafeIFC $ do return (MkLbl x)

protectx :: SPrin l -> a -> IFC pc l a
protectx l x = UnsafeIFC $ do return (MkLbl x)

relabel  :: (pc ⊑ pc', l ⊑ l')  => IFC pc l a -> IFC pc' l' a 
relabel x = UnsafeIFC $ do a <- runIFC x;
                           --return . relabel a  -- this didn't work. why?
                           return $ MkLbl (unsafeRunLbl a)

--relabelx :: (l ⊑ l') => SPrin l -> SPrin l' -> IFC pc l a -> IFC pc l' a 
--relabelx l l' x = UnsafeIFC $ do
--                           a <- runIFC x;
--                           --return . relabel a  -- this didn't work. why?
--                           return $ MkLbl (unsafeRunLbl a)
--
--relabelxx  :: (pc ⊑ pc', l ⊑ l') => SPrin pc' -> SPrin l' -> IFC pc l a -> IFC pc' l' a 
--relabelxx pc' l' x = UnsafeIFC $ do
--                              a <- runIFC x;
--                              return $ MkLbl (unsafeRunLbl a)

assume :: (pc ≽ Voice q, Voice (C p) ≽ Voice (C q)) =>
            (p :≽ q) -> ((p ≽ q) => IFC pc l a) -> IFC pc l a
assume pf m = unsafeAssume pf m
-}
