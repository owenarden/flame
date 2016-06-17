{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

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

data ActsForProof =                    
      AFTop
    | AFBot
    | AFRefl 
    | AFDel (Prin, Prin) -- NB: this implicitly uses transitivity on given dels
    | AFConj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFDisj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
  deriving (Read, Eq, Show, Data, Typeable)
