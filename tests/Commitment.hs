{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module Commitments where

import Flame.Type.Principals
import Flame.Data.Principals
import Flame.Type.IFC 

class Commitment a where
  commit  :: Monad e => SPrin p -> IFC e (I p) (C p) a -> IFC e (I p) p a
  receive :: Monad e => SPrin p -> SPrin q -> IFC e (I q) p a -> IFC e (I q) (p ∧ (I q)) a
  open    :: Monad e => SPrin p -> SPrin q -> IFC e (I p) (p ∧ (I q)) a -> IFC e (I p) ((I p) ∧ q) a

i_commit :: Monad e => SPrin p -> IFC e (I p) (C p) a -> IFC e (I p) p a
i_commit p v = assume ((SBot*←) ≽ (p*←)) (reprotect v)

i_receive :: Monad e => SPrin p -> SPrin q -> IFC e (I q) p a -> IFC e (I q) (p ∧ (I q)) a
i_receive p q v = assume (p ≽ (q*←)) (reprotect v)

-- i_receive2 :: Monad e => SPrin p -> SPrin q -> IFC e (I q) p a -> IFC e (I q) (p ∧ (I q)) a
-- i_receive2 p q v = apply v $ \x' -> assume (p ≽ (q^←)) $ lbind x' (protectx (((⊤)^→) ∧ ((⊥)^←)) (p' ∧ (q'^←)))
--   where
--     p' = (st p)
--     q' = (st q)

i_open :: Monad e => SPrin p -> SPrin q -> IFC e ((∇) p) (p ∧ (I q)) a -> IFC e ((∇) p) ((I p) ∧ q) a
i_open p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (reprotect v)
