{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module Commitments where

import Flame.Principals
import Flame.IFC as M

commit :: FLA m e n => SPrin p -> m e n (I p) (C p) a -> m e n (I p) p a
commit p v = assume ((SBot*←) ≽ (p*←)) (M.reprotect v)

receive :: FLA m e n => SPrin p -> SPrin q -> m e n (I q) p a -> m e n (I q) (p ∧ (I q)) a
receive p q v = assume (p ≽ (q*←)) (M.reprotect v)

{- does compile -}
bad_receive :: FLA m e n => SPrin p -> SPrin q -> m e n (I q) (p ∧ C q) a -> m e n (I q) (p ∧ q) a
bad_receive p q v = assume (p ≽ (q*←)) (M.reprotect v)

open :: FLA m e n => SPrin p -> SPrin q -> m e n ((∇) p) (p ∧ (I q)) a -> m e n ((∇) p) ((I p) ∧ q) a
open p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (M.reprotect v)

--{- Forced to commit only public data. committing it makes it secret. -}
--{- Alternative: with higher integrity pc, could declass, then endorse. -}
--nm_commit :: (NMFLA m n, p ⊑ Δ p) =>
--             SPrin p
--             -> m n (Δ KBot) (I p) KBot a
--             -> m n (Δ KBot) (I p) p a
--nm_commit p v = iassume ((SBot*←) ≽ (p*←)) (NM.reprotect (SEye SBot) v)
--
--nm_receive :: (NMFLA m n, p ⊑ Δ p) =>
--              SPrin p
--              -> SPrin q
--              -> m n (Δ p) (I q) p a -> m n (Δ p) (I q) (p ∧ (I q)) a
--nm_receive p q v = iassume ((p*←) ≽ (q*←)) (NM.reprotect (SEye p) v)
--
--{- does not compile 
--nm_badreceive :: (NMFLA m n, p ⊑ Δ p) =>
--                 SPrin p
--                 -> SPrin q
--                 -> m n (Δ p) (I q) (p ∧ C q) a
--                 -> m n (Δ p) (I q) (p ∧ q) a
--nm_badreceive p q v = iassume ((p*←) ≽ (q*←)) (NM.reprotect (SEye p) v)
---}
--nm_open :: NMFLA m n =>
--           SPrin p
--           -> SPrin q
--           -> m n (C q) ((∇) p) (p ∧ (I q)) a
--           -> m n (C q) ((∇) p) ((I p) ∧ q) a
--nm_open p q v = iassume ((((*∇) (q))*←) ≽ (((*∇) (p))*←)) $
--                 cassume ((q*→) ≽ (p*→)) (NM.reprotect (q*→) v)
