{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module Flame.Type.Assert
where
  
import Flame.Type.Principals
assertEq :: (l === l') => SPrin l -> SPrin l' -> ()
assertEq l l' = ()

assertActsFor :: (p ≽ q) => SPrin p -> SPrin q -> ()
assertActsFor p q = ()

assertFlowsTo :: (l ⊑ l') => SPrin l -> SPrin l' -> ()
assertFlowsTo l l' = ()
