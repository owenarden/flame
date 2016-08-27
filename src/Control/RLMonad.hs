{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.RLMonad where

import Prelude hiding (fmap, pure, (<*>), return, (>>=))
import qualified Prelude as M
import Data.Constraint
import Control.Monad.IO.Class

class RLFunctor (f :: k -> * -> *) where
  type MayUse f (i::k) a (j::k) b :: Constraint
  type MayUse f i a j b = ()
  type Suitable f a :: Constraint
  type Suitable f a = ()
  fmap :: (Suitable f a, Suitable f b, MayUse f i a j b) => (a -> b) -> f i a -> f j b

class RLFunctor f => RLApplicative (f :: k -> * -> *) where
  pure :: Suitable f a => a -> f i a
  (<*>) :: (Suitable f a, Suitable f b, MayUse f i a j b) =>
           f j (a -> b) -> f i a -> f j b

class RLApplicative m => RLMonad (m :: k -> * -> *) where
  return :: Suitable m a => a -> m i a
  (>>=) :: (Suitable m a, Suitable m b, MayUse m i a j b) =>
           m i a -> (a -> m j b) -> m j b

newtype LiftR f (i :: *) a = LiftR { unLiftR :: f a }

instance Functor f => RLFunctor (LiftR f) where
  type Suitable (LiftR f) a = ()
  type MayUse (LiftR f) i a j b = ()
  fmap g (LiftR a) = LiftR $ M.fmap g $ a

instance Applicative f => RLApplicative (LiftR f) where
  pure = LiftR . M.pure
  (<*>) (LiftR g) (LiftR a) =  LiftR (g M.<*> a)

instance Monad m => RLMonad (LiftR m) where
  return = LiftR . M.return
  (>>=) (LiftR a) g = LiftR $ a M.>>= (\a' -> unLiftR $ g a')

instance RLFunctor (LiftR f) => Functor (LiftR f i) where
  fmap g a = unLiftR $ Control.RLMonad.fmap g (LiftR a)

instance RLApplicative (LiftR f) => Applicative (LiftR f i) where
  pure a = unLiftR $ Control.RLMonad.pure a
  (<*>) g a =  unLiftR $ (LiftR g) Control.RLMonad.<*> (LiftR a)

instance RLMonad (LiftR m) => Monad (LiftR m i) where
  return a = unLiftR $ Control.RLMonad.return a
  (>>=) a f =  unLiftR $ (LiftR a) Control.RLMonad.>>= (\a' -> LiftR $ f a')
  -- XXX: bug? omiting this causes a hang for sequential actions
  -- This (usually redundant) definition is necessary for some reason,
  -- possibly related to the do-syntax expanding to the wrong >>=
  m >> k = m Control.RLMonad.>>= \_ -> k

instance MonadIO (LiftR IO i) where 
  liftIO = LiftR
