{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

import Flame.Type.Principals
--import Flame.Type.IFC
import Flame.Type.Assert

eqTTrans :: (p ⊑ q, q ⊑ r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans p q r = assertEq p r

eqTSym :: (l === l', l'' === l') => SPrin l -> SPrin l' -> SPrin l'' -> ()
eqTSym l l' l'' = assertEq l' l

eqTDisjAbsorb :: SPrin p -> SPrin q -> ()
eqTDisjAbsorb p q = assertEq (p *∧ (p *∨ q)) p 

main :: IO ()
main = print "hello"--(test1 ++ test2 ++ (test3 STop)) 
