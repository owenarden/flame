{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module Commitments where

import Flame.Type.Principals
import Flame.Type.IFC 

class Commitment a where
  commit  :: Monad e => SPrin p -> IFC e (I p) (C p) a -> IFC e (I p) p a
  receive :: Monad e => SPrin p -> SPrin q -> IFC e (I q) p a -> IFC e (I q) (p ∧ (I q)) a
  open    :: Monad e => SPrin p -> SPrin q -> IFC e (I p) (p ∧ (I q)) a -> IFC e (I p) ((I p) ∧ q) a

i_commit :: Monad e => SPrin p -> IFC e (I p) (C p) a -> IFC e (I p) p a
i_commit p v = assume ((pbot^←) ≽ (p^←)) (relabel v)

i_receive :: Monad e => SPrin p -> SPrin q -> IFC e (I q) p a -> IFC e (I q) (p ∧ (I q)) a
i_receive p q v = assume (p ≽ (q^←)) (relabel v)

i_open :: Monad e => SPrin p -> SPrin q -> IFC e (Voice p) (p ∧ (I q)) a -> IFC e (Voice p) ((I p) ∧ q) a
i_open p q v = assume (voice (q^→) ≽ voice (p^→)) $ assume ((q^→) ≽ (p^→)) (relabel v)
