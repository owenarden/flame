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
