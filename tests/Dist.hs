{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module Dist where
import Flame.Principals
import Flame.Assert

eqTConjDistDisj :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjDistDisj p q r = assertEq (p ∧ (q ∨ r)) ((p ∧ q) ∨ (p ∧ r))
