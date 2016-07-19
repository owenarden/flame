{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

import Flame.Type.Principals
import Flame.Type.IFC
import Flame.Type.Assert

type Alice = KName "Alice"
type Bob = KName "Bob"

test1 :: (KTop ≽ KBot) => String
test1 = "Hello"
test2 :: (((C KBot) ∧ (I KTop)) ⊑ ((C KTop) ∧ (I KBot))) => String
test2 = "World"
test3 :: (p ⊑ p) => SPrin p -> String
test3 p = "World"

test4 :: (Alice ≽ Bob) => String
test4 = "World"

test5 :: (KBot ≽ KTop) => String
test5 = test1

eqTSym :: (l === l') => SPrin l -> SPrin l' -> ()
eqTSym l l' = assertEq l' l

eqTTrans :: (p === q, q === r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans p q r = assertEq p r

eqTConjComm :: SPrin p -> SPrin q -> ()
eqTConjComm p q = assertEq (p ∧ q) (q ∧ p) 

eqTDisjComm :: SPrin p -> SPrin q -> ()
eqTDisjComm p q = assertEq (p ∨ q) (q ∨ p) 

eqTConjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjAssoc p q r = assertEq ((p ∧ q) ∧ r) (p ∧ (q ∧ r))

eqTDisjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTDisjAssoc p q r = assertEq ((p ∨ q) ∨ r) (p ∨ (q ∨ r))

eqTDisjAbsorb :: SPrin p -> SPrin q -> ()
eqTDisjAbsorb p q = assertEq (p ∧ (p ∨ q)) p 
                    
eqTConjAbsorb :: SPrin p -> SPrin q -> ()
eqTConjAbsorb p q = assertEq (p ∨ (p ∧ q)) p 

eqTConjIdemp :: SPrin p -> ()
eqTConjIdemp p = assertEq (p ∧ p) p 

eqTDisjIdemp :: SPrin p -> ()
eqTDisjIdemp p = assertEq (p ∨ p) p 

eqTConjIdent :: SPrin p -> ()
eqTConjIdent p = assertEq (p ∧ pbot) p 
                 
eqTDisjIdent :: SPrin p -> ()
eqTDisjIdent p = assertEq (p ∨ ptop) p 

eqTConjTop :: SPrin p -> ()
eqTConjTop p = assertEq (p ∧ ptop) ptop 
       
eqTDisjBot :: SPrin p -> ()
eqTDisjBot p = assertEq (p ∨ pbot) pbot

eqTConjDistDisj :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjDistDisj p q r = assertEq (p ∧ (q ∨ r)) ((p ∧ q) ∨ (p ∧ r))

eqTConjConf :: SPrin p -> SPrin q -> ()
eqTConjConf p q = assertEq ((p ∧ q)^→) ((p^→) ∧ (q^→))

eqTConjInteg :: SPrin p -> SPrin q -> ()
eqTConjInteg p q = assertEq ((p ∧ q)^←) ((p^←) ∧ (q^←))

eqTDisjConf :: SPrin p -> SPrin q -> ()
eqTDisjConf p q = assertEq ((p ∨ q)^→) ((p^→) ∨ (q^→))

eqTDisjInteg :: SPrin p -> SPrin q -> ()
eqTDisjInteg p q = assertEq ((p ∨ q)^←) ((p^←) ∨ (q^←))

eqTConfIdemp :: SPrin p -> ()
eqTConfIdemp p = assertEq ((p^→)^→) (p^→)

eqTIntegIdemp :: SPrin p -> ()
eqTIntegIdemp p = assertEq ((p^←)^←) (p^←)

eqTConfInteg :: SPrin p -> ()
eqTConfInteg p = assertEq ((p^→)^←) pbot

eqTIntegConf :: SPrin p -> ()
eqTIntegConf p = assertEq ((p^←)^→) pbot

eqTConfDisjInteg :: SPrin p -> SPrin q -> ()
eqTConfDisjInteg p q = assertEq ((p^→) ∨ (q^←)) pbot

eqTConfIntegBasis :: SPrin p -> ()
eqTConfIntegBasis p = assertEq ((p^←) ∧ (p^→)) p

eqTBotConf :: ()
eqTBotConf = assertEq (pbot^→) pbot

eqTBotInteg :: ()
eqTBotInteg = assertEq (pbot^←) pbot

--assertCBT0 :: (I (C KBot) ≽ I (C KTop)) => ()
--assertCBT0 = ()
--testCBT0 = withTrans ((pbot^→)^←) pbot ((ptop^→)^←) assertCBT0

assertCBT1 :: (I (C KBot) ≽ KBot) => ()
assertCBT1 = ()
testCBT1 = assertCBT1

assertCBT2 :: (KBot ≽ I (C KTop)) => ()
assertCBT2 = ()
testCBT2 = assertCBT2

assertCBT :: (C KBot ⊑ C KTop) => ()
assertCBT = ()
testCBT = assertCBT

assertRCV :: (((C p) ∧ (I p)) ⊑ (p ∧ (I KBot))) => SPrin p -> ()
assertRCV p = ()
testRCV = assertRCV

----assertCBT2 :: (ActsFor (C (C KTop)) (C (C KBot)), ActsFor (I (C KBot)) (I (C KTop))) => ()
----assertCBT2 = ()
----testCBT2 = assertCBT2 -- should be possible with withTrans
--
--assertITB :: FlowsTo (I KTop) (I KBot) => ()
--assertITB = ()
--testITB = assertITB
--
--neg_flTConf ::  SPrin p -> ()
--neg_flTConf p = assertFlowsTo ((p^→) ∧ (SBot^←)) p
--
--neg_flTConf2 ::  SPrin p -> SPrin q -> ()
--neg_flTConf2 p q = assertActsFor SBot (SConf q) --(p^→) 
--
--neg_flTInteg ::  SPrin p -> SPrin q -> ()
--neg_flTInteg p q = assertActsFor (p^→) ((p^→) ∧ (q^←))
--
flTConfConjL :: SPrin p ->  SPrin q -> ()
flTConfConjL p q = assertFlowsTo (p^→) ((p ∧ q)^→)  

main :: IO ()
main = print test1 --(test1 ++ test2 ++ (test3 STop)) 
