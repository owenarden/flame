{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module Commitments where

import Flame.Principals
import Flame.IFC 

class Commitment a where
  commit  :: SPrin p -> IFC (I p) (C p) a -> IFC (I p) p a
  receive :: SPrin p -> SPrin q -> IFC (I q) p a -> IFC (I q) (p ∧ (I q)) a
  open    :: SPrin p -> SPrin q -> IFC (I p) (p ∧ (I q)) a -> IFC (I p) ((I p) ∧ q) a

i_commit :: SPrin p -> IFC (I p) (C p) a -> IFC (I p) p a
i_commit p v = assume ((pbot^←) ≽ (p^←)) (relabel v)

i_receive :: SPrin p -> SPrin q -> IFC (I q) p a -> IFC (I q) (p ∧ (I q)) a
i_receive p q v = assume (p ≽ (q^←)) (relabel v)

i_open :: SPrin p -> SPrin q -> IFC (Voice p) (p ∧ (I q)) a -> IFC (Voice p) ((I p) ∧ q) a
i_open p q v = assume (voice (q^→) ≽ voice (p^→)) $ assume ((q^→) ≽ (p^→)) (relabel v)
