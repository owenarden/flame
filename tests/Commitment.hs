{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module Commitments where

import Flame.Type.Principals
import Flame.Data.Principals
import Flame.Type.IFC as M
import Flame.Type.TCB.NMIFC as NM

commit :: FLA m n => SPrin p -> m n (I p) (C p) a -> m n (I p) p a
commit p v = assume ((SBot*←) ≽ (p*←)) (M.reprotect v)

receive :: FLA m n => SPrin p -> SPrin q -> m n (I q) p a -> m n (I q) (p ∧ (I q)) a
receive p q v = assume (p ≽ (q*←)) (M.reprotect v)

open :: FLA m n => SPrin p -> SPrin q -> m n ((∇) p) (p ∧ (I q)) a -> m n ((∇) p) ((I p) ∧ q) a
open p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (M.reprotect v)

nm_commit :: NMFLA m n => SPrin p -> m n β (I p) (C p) a -> m n β (I p) p a
nm_commit p v = iassume ((SBot*←) ≽ (p*←)) (NM.reprotect v)

nm_receive :: NMFLA m n => SPrin p -> SPrin q -> m n β (I q) p a -> m n β (I q) (p ∧ (I q)) a
nm_receive p q v = iassume ((p*←) ≽ (q*←)) (NM.reprotect v)

nm_open :: NMFLA m n => SPrin p -> SPrin q -> m n β ((∇) p) (p ∧ (I q)) a -> m n β ((∇) p) ((I p) ∧ q) a
nm_open p q v = iassume ((*∇) (q) ≽ (*∇) (p)) $ cassume ((q*→) ≽ (p*→)) (NM.reprotect v)

--i_receive :: Monad e => SPrin p -> SPrin q -> IFC e (I q) p a -> IFC e (I q) (p ∧ (I q)) a

-- i_receive2 :: Monad e => SPrin p -> SPrin q -> IFC e (I q) p a -> IFC e (I q) (p ∧ (I q)) a
-- i_receive2 p q v = apply v $ \x' -> assume (p ≽ (q^←)) $ lbind x' (protectx (((⊤)^→) ∧ ((⊥)^←)) (p' ∧ (q'^←)))
--   where
--     p' = (st p)
--     q' = (st q)
