{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes#-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

-- This test case exercised a bug that demonstrated the need to 
-- be able to return Nothing when normalizing principals.

import Flame.Principals

class FLA m where
  f   :: a -> m pc a
  g :: (pc ≽ pc') => m pc a -> (a -> m pc' b)
  h :: forall pc pc' a. (pc ≽ pc') => m pc' a 
  h = g (f :: a -> m pc a)
  
main :: IO ()
main = undefined
