{-# LANGUAGE DeriveDataTypeable #-}

module Flame.Principals.Dynamic
where
import Data.Data

{- The principal data type -}
data Prin =
  Top
  | Bot
  | Name String
  | Conj  Prin Prin 
  | Disj  Prin Prin
  | Conf  Prin
  | Integ Prin
  | Voice Prin
  deriving (Read, Eq, Show, Data, Typeable)

