{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
--{-# OPTIONS_GHC -fdefer-type-errors -fplugin Flame.Solver #-}

import Flame.Assert
import Flame.Principals
import Flame.Runtime.Principals

import Control.DeepSeq (force, NFData)
import Control.Exception (evaluate, try, throwIO, TypeError(..))
import Test.ShouldNotTypecheck
import Test.Tasty
import Test.Tasty.HUnit
       
eqTSym :: (l === l') => SPrin l -> SPrin l' -> ()
eqTSym l l' = assertEq l l'

eqTTrans :: (p ≽ q, q ≽ r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans p q r = assertActsFor p r

eqTTrans2 :: (p ≽ q, q ≽ r, r ≽ q, q ≽ p) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans2 p q r = assertEq p r

eqTTrans3 :: (p ⊑ q, q ⊑ r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans3 p q r = assertFlowsTo p r

eqTTrans4 :: (p === q, q === r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans4 p q r = assertEq p r

eqTConjComm :: SPrin p -> SPrin q -> ()
eqTConjComm p q = assertEq (p *∧ q) (q *∧ p) 

eqTDisjComm :: SPrin p -> SPrin q -> ()
eqTDisjComm p q = assertEq (p *∨ q) (q *∨ p) 

eqTConjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjAssoc p q r = assertEq ((p *∧ q) *∧ r) (p *∧ (q *∧ r))

eqTDisjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTDisjAssoc p q r = assertEq ((p *∨ q) *∨ r) (p *∨ (q *∨ r))

eqTDisjAbsorb :: SPrin p -> SPrin q -> ()
eqTDisjAbsorb p q = assertEq (p *∧ (p *∨ q)) p 
                    
eqTConjAbsorb :: SPrin p -> SPrin q -> ()
eqTConjAbsorb p q = assertEq (p *∨ (p *∧ q)) p 

eqTConjIdemp :: SPrin p -> ()
eqTConjIdemp p = assertEq (p *∧ p) p 

eqTDisjIdemp :: SPrin p -> ()
eqTDisjIdemp p = assertEq (p *∨ p) p 

eqTConjIdent :: SPrin p -> ()
eqTConjIdent p = assertEq (p *∧ SBot) p 
                 
eqTDisjIdent :: SPrin p -> ()
eqTDisjIdent p = assertEq (p *∨ STop) p 

eqTConjTop :: SPrin p -> ()
eqTConjTop p = assertEq (p *∧ STop) STop 
       
eqTDisjBot :: SPrin p -> ()
eqTDisjBot p = assertEq (p *∨ SBot) SBot

eqTConjDistDisj :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjDistDisj p q r = assertEq (p *∧ (q *∨ r)) ((p *∧ q) *∨ (p *∧ r))

eqTConjConf :: SPrin p -> SPrin q -> ()
eqTConjConf p q = assertEq ((p *∧ q)*→) ((p*→) *∧ (q*→))

eqTConjInteg :: SPrin p -> SPrin q -> ()
eqTConjInteg p q = assertEq ((p *∧ q)*←) ((p*←) *∧ (q*←))

eqTDisjConf :: SPrin p -> SPrin q -> ()
eqTDisjConf p q = assertEq ((p *∨ q)*→) ((p*→) *∨ (q*→))

eqTDisjInteg :: SPrin p -> SPrin q -> ()
eqTDisjInteg p q = assertEq ((p *∨ q)*←) ((p*←) *∨ (q*←))

eqTConfIdemp :: SPrin p -> ()
eqTConfIdemp p = assertEq ((p*→)*→) (p*→)

eqTIntegIdemp :: SPrin p -> ()
eqTIntegIdemp p = assertEq ((p*←)*←) (p*←)

eqTConfInteg :: SPrin p -> ()
eqTConfInteg p = assertEq ((p*→)*←) SBot

eqTIntegConf :: SPrin p -> ()
eqTIntegConf p = assertEq ((p*←)*→) SBot

eqTConfDisjInteg :: SPrin p -> SPrin q -> ()
eqTConfDisjInteg p q = assertEq ((p*→) *∨ (q*←)) SBot

eqTConfIntegBasis :: SPrin p -> ()
eqTConfIntegBasis p = assertEq ((p*←) *∧ (p*→)) p

eqTBotConf :: ()
eqTBotConf = assertEq (SBot*→) SBot

eqTBotInteg :: ()
eqTBotInteg = assertEq (SBot*←) SBot
 
--assertCBT0 :: (I (C KBot) ≽ I (C KTop)) => ()
--assertCBT0 = ()
--testCBT0 = withTrans ((SBot*→)*←) SBot ((STop*→)*←) assertCBT0

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
--neg_flTConf p = assertFlowsTo ((p*→) *∧ (SBot*←)) p
--
--neg_flTConf2 ::  SPrin p -> SPrin q -> ()
--neg_flTConf2 p q = assertActsFor SBot (SConf q) --(p*→) 
--
--neg_flTInteg ::  SPrin p -> SPrin q -> ()
--neg_flTInteg p q = assertActsFor (p*→) ((p*→) *∧ (q*←))
--
flTConfConjL :: SPrin p ->  SPrin q -> ()
flTConfConjL p q = assertFlowsTo (p*→) ((p *∧ q)*→)  

main :: IO ()
main = undefined

--main = defaultMain tests
-- XXX the below should supposedly work, but doesn't seem to...
---- The type for GHC-8.0.1 is a hack, see https://github.com/CRogers/should-not-typecheck/pull/6#issuecomment-211520177
--shouldTypecheck :: NFData a => (() ~ ()) => a -> Assertion
--shouldTypecheck a = do
--  result <- try (evaluate $ force a)
--  case result of
--    Right _ -> return ()
--    Left e@(TypeError msg) -> assertFailure msg

-- tests :: TestTree
-- tests = testGroup "flame"
--   [ testGroup "Equality constraint tests"
--     [ testCase "eqTSym" $
--       shouldTypecheck (eqTSym SBot STop),
--       testCase "eqTTrans" $
--       shouldTypecheck $ (eqTTrans STop SBot SBot) == ()
--       --testCase "eqTTrans'" $ shouldTypecheck (eqTTrans STop (st p) (st q)), 
--       --testCase "eqTTrans2" $ shouldTypecheck (eqTTrans2 SBot SBot SBot), 
--       --testCase "eqTTrans3" $ shouldTypecheck (eqTTrans3 SBot SBot SBot), 
--       --testCase "eqTTrans4" $ shouldTypecheck (eqTTrans4 SBot SBot SBot), 
--       --testCase "eqTConjComm" $ shouldTypecheck (eqTConjComm SBot SBot), 
--       --testCase "eqTDisjComm" $ shouldTypecheck (eqTDisjComm SBot SBot), 
--       --testCase "eqTConjAssoc" $ shouldTypecheck (eqTConjAssoc SBot SBot SBot), 
--       --testCase "eqTDisjAssoc" $ shouldTypecheck (eqTDisjAssoc SBot SBot SBot), 
--       --testCase "eqTDisjAbsorb" $ shouldTypecheck (eqTDisjAbsorb SBot SBot), 
--       --testCase "eqTConjAbsorb" $ shouldTypecheck (eqTConjAbsorb SBot SBot), 
--       --testCase "eqTConjIdemp" $ shouldTypecheck (eqTConjIdemp SBot), 
--       --testCase "eqTDisjIdemp" $ shouldTypecheck (eqTDisjIdemp SBot), 
--       --testCase "eqTConjIdent" $ shouldTypecheck (eqTConjIdent SBot), 
--       --testCase "eqTDisjIdent" $ shouldTypecheck (eqTDisjIdent SBot), 
--       --testCase "eqTConjTop" $ shouldTypecheck (eqTConjTop SBot), 
--       --testCase "eqTDisjBot" $ shouldTypecheck (eqTDisjBot SBot), 
--       --testCase "eqTConjDistDisj" $ shouldTypecheck (eqTConjDistDisj SBot SBot SBot), 
--       --testCase "eqTConjConf" $ shouldTypecheck (eqTConjConf SBot SBot), 
--       --testCase "eqTConjInteg" $ shouldTypecheck (eqTConjInteg SBot SBot), 
--       --testCase "eqTDisjConf" $ shouldTypecheck (eqTDisjConf SBot SBot), 
--       --testCase "eqTDisjInteg" $ shouldTypecheck (eqTDisjInteg SBot SBot), 
--       --testCase "eqTConfIdemp" $ shouldTypecheck (eqTConfIdemp SBot), 
--       --testCase "eqTIntegIdemp" $ shouldTypecheck (eqTIntegIdemp SBot), 
--       --testCase "eqTConfInteg" $ shouldTypecheck (eqTConfInteg SBot), 
--       --testCase "eqTIntegConf" $ shouldTypecheck (eqTIntegConf SBot), 
--       --testCase "eqTConfDisjInteg" $ shouldTypecheck (eqTConfDisjInteg SBot SBot), 
--       --testCase "eqTConfIntegBasis" $ shouldTypecheck (eqTConfIntegBasis SBot), 
--       --testCase "eqTBotConf" $ shouldTypecheck (eqTBotConf ), 
--       --testCase "eqTBotInteg" $ shouldTypecheck (eqTBotInteg)
--     ]
--   ]
