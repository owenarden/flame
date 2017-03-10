{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module TestNMIFC where

import Flame.Principals
import Flame.Runtime.Principals
import Flame.IFC 

one :: FLA m e n => SPrin p -> SPrin q
       -> m e n (I q) (C p ∧ (I (p ∨ q))) a
       -> m e n (I q) (C p ∧ I q) a
one p q v = assume ((p*←) ≽ (q*←)) (reprotect v)

{- #1 -}                             
nm_one :: (BFLA c m e n, p ⊑ Δ p) =>
       SPrin p -> SPrin q
       -> c m e n (Δ p) (I q) (C p ∧ (I (p ∨ q))) a
       -> c m e n (Δ p) (I q) (C p ∧ I q) a
nm_one p q v = iassume ((p*←) ≽ (q*←)) (reprotect_b v)

two :: FLA m e n => SPrin p -> SPrin q
       -> m e n (I p) (C p ∧ (I (p ∨ q))) a
       -> m e n (I p) p a
two p q v = assume ((q*←) ≽ (p*←)) (reprotect v)

{- #2 -}
{- Fails (as desired): "Could not deduce (C (Δ q) ≽ C (C p ∧ I (p ∨ q)))"
nm_two :: (BFLA c m e n, q ⊑ Δ q) => SPrin p -> SPrin q
       -> c m e n (Δ q) (I p) (C p ∧ (I (p ∨ q))) a
       -> c m e n (Δ q) (I p) p a
nm_two p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)
-}

three :: FLA m e n => SPrin p -> SPrin q
       -> m e n ((∇) q) (C (p ∧ q) ∧ (I q)) a
       -> m e n ((∇) q) (C p ∧ I q)  a
three p q v = assume ((*∇) (p) ≽ (*∇) (q)) $
                assume ((p*→) ≽ (q*→)) (reprotect v)

{- #3 -}
nm_three :: (BFLA c m e n, p ~ N p', q ~ N q') => SPrin p -> SPrin q
       -> c m e n (Δ ((∇) p) ∧ I q) ((∇) q) (C (p ∧ q) ∧ I q) a
       -> c m e n (Δ ((∇) p) ∧ I q) ((∇) q) (C p ∧ I q) a
nm_three p q v = vassume ((*∇) (p) ≽ ((*∇) (q))) $
                  cassume ((p*→) ≽ (q*→)) (reprotect_b v)

four :: FLA m e n => SPrin p -> SPrin q
       -> m e n ((∇) p) (C (p ∧ q) ∧ (I q)) a
       -> m e n ((∇) p) q  a
four p q v = assume ((*∇) (q) ≽ (*∇) (p)) $
                assume ((q*→) ≽ (p*→)) (reprotect v)

{- #4 (allowed) google doc says this is insecure 
 -   only types if p and q are primitive..
 - -}
nm_four :: (BFLA c m e n, q ⊑ Δ q, p ~ N p', q ~ N q') => SPrin p -> SPrin q
       -> c m e n (Δ ((∇) q) ∧ I q) ((∇) p) (C (p ∧ q) ∧ I q) a
       -> c m e n (Δ ((∇) q) ∧ I q) ((∇) p) q a
nm_four p q v = vassume ((*∇) (q) ≽ ((*∇) (p))) $
                  cassume ((q*→) ≽ (p*→)) (reprotect_b v)

five :: FLA m e n => SPrin p 
       -> m e n (I p) (C p) a
       -> m e n (I p) p  a
five p v = assume (((SBot)*←) ≽ (p*←)) (reprotect v)

{- #5 not allowed.  This endorsement is malleable. -}
{-
nm_five :: BFLA m e n => SPrin p 
       -> c m e n (Δ KBot) (I p) (C p) a
       -> c m e n (Δ KBot) (I p) p  a
nm_five p v = iassume (((SBot)*←) ≽ (p*←)) (reprotect_b v)
-}
{- #5 Alternative 1: Commit only public data. committing it makes it secret. -}
nm_five' :: BFLA c m e n => SPrin p 
       -> c m e n (Δ KBot) (I p) KBot a
       -> c m e n (Δ KBot) (I p) p  a
nm_five' p v = iassume (((SBot)*←) ≽ (p*←)) (reprotect_b v)

{- #5 Alternative 2: with higher integrity pc, could declass, then endorse.
   seems a little weird, but this is what explicitly permitting malleability
   looks like, I suppose
NB: this doesn't work yet, but might with some extra reasoning in the solver
nm_five'' :: (BFLA c m e n, p ⊑ Δ p) => SPrin p 
       -> c m e n (Δ p ∧ C p) (I p ∧ ((∇) p)) (C p) a
       -> c m e n (Δ p ∧ C p) (I p ∧ ((∇) p)) p  a
nm_five'' p v = vassume ((*∇)(SBot*→) ≽ (*∇)(p*→)) $
                 eassume (SEye SBot ≽ SEye p) $
                  cassume ((SBot*→) ≽ (p*→)) $
                   iassume ((SBot*←) ≽ (p*←)) $ (reprotect_b v)
-}

six :: FLA m e n => SPrin p -> SPrin q -> m e n (I q) (p ∧ C q) a -> m e n (I q) (p ∧ q) a
six p q v = assume (p ≽ (q*←)) (reprotect v)
{- #6 this is badreceive from Commitment.hs -}
{- Fails (as desired)
nm_six :: (BFLA c m e n, p ⊑ Δ p) =>
                 SPrin p
                 -> SPrin q
                 -> c m e n (Δ p) (I q) (p ∧ C q) a
                 -> c m e n (Δ p) (I q) (p ∧ q) a
nm_six p q v = iassume ((p*←) ≽ (q*←)) (reprotect_b v)
-}

seven :: FLA m e n => SPrin p -> SPrin q -> m e n (I p) (C p ∧ I q) a -> m e n (I p) (p ∧ I q) a
seven p q v = assume (q ≽ (p*←)) (reprotect v)
{- #7 this is similar to badreceive -}
{- Fails (as desired)
nm_seven :: (BFLA c m e n) =>
                 SPrin p
                 -> SPrin q
                 -> m e n (Δ q) (I p) (C p ∧ I q) a
                 -> m e n (Δ q) (I p) (p ∧ I q) a
nm_seven p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)
-}

{- #8 this is similar to battleship -}
eight :: FLA m e n =>
         SPrin p
      -> SPrin q
      -> m e n (I p) (C (p ∨ q) ∧ I q) a
      -> m e n (I p) (C (p ∨ q) ∧ I (p ∧ q)) a
eight p q v = assume (q ≽ (p*←)) (reprotect v)
nm_eight :: (BFLA c m e n, q ⊑ Δ q) =>
                 SPrin p
                 -> SPrin q
                 -> c m e n (Δ q) (I p) (C (p ∨ q) ∧ I q) a
                 -> c m e n (Δ q) (I p) (C (p ∨ q) ∧ I (p ∧ q)) a
nm_eight p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)

{- #9 is same as #5 (commit) -}

                                   
{- #10 is open from Commitment.hs -}
ten :: FLA m e n => SPrin p -> SPrin q -> m e n ((∇) p) (p ∧ (I q)) a -> m e n ((∇) p) ((I p) ∧ q) a
ten p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (reprotect v)

nm_ten :: (BFLA c m e n, p ~ N p', q ~ N q') =>
           SPrin p
           -> SPrin q
           -> c m e n (C (p ∨ q) ∧ I p ∧ ((∇) q)) ((∇) p) (p ∧ (I q)) a
           -> c m e n (C (p ∨ q) ∧ I p ∧ ((∇) q)) ((∇) p) ((I p) ∧ q) a
nm_ten p q v = vassume (((*∇) (q)) ≽ ((*∇) p)) $ 
                 cassume ((q*→) ≽ (p*→)) 
                  (reprotect_b v)

{- #11 -}
eleven :: (FLA m e n, r ≽ q) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m e n ((∇) p) (p ∧ (I q)) a
          -> m e n ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
eleven p q r v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (reprotect v)

--Broken by cassume integrity constraint                                                                 
nm_eleven :: (BFLA c m e n, r ≽ q, p ~ N p', q ~ N q', r ~ N r') =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> c m e n (C q ∧ I p ∧ I q) ((∇) p) (p ∧ (I q)) a
           -> c m e n (C q ∧ I p ∧ I q) ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
nm_eleven p q r v = iassume ((((*∇) (q))*←) ≽ (((*∇) (p))*←)) $
                 cassume ((q*→) ≽ (p*→)) (reprotect_b v)

{- #12 -}
twelve :: (FLA m e n, r ≽ q) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m e n ((∇) p) (I p ∧ q) a
          -> m e n ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
twelve p q r v = reprotect v
nm_twelve :: (BFLA c m e n, r ≽ q) =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> c m e n (C q) ((∇) p) (I p ∧ q) a
           -> c m e n (C q) ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
nm_twelve p q r v = reprotect_b v

{- #13 -}
thirteen :: (FLA m e n, q ⊑ r) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m e n pc (I p ∧ q) a
          -> m e n pc (I p ∧ r) a
thirteen p q r v = reprotect v
nm_thirteen :: (BFLA c m e n, q ⊑ r) =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> c m e n (C q) pc (I p ∧ q) a
           -> c m e n (C q) pc (I p ∧ r) a
nm_thirteen p q r v = reprotect_b v




--nm_four :: (BFLA c m e n, q ⊑ Δ q) => SPrin p -> SPrin q
--       -> c m e n (Δ ((∇) q)) ((∇) p) (C (p ∧ q) ∧ I q) a
--       -> c m e n (Δ ((∇) q)) ((∇) p) q a
--nm_receive :: (BFLA c m e n, p ⊑ Δ p) =>
--              SPrin p
--              -> SPrin q
--              -> c m e n (Δ p) (I q) p a
--              -> c m e n (Δ p) (I q) (p ∧ (I q)) a
--nm_six :: (BFLA c m e n, p ⊑ Δ p) =>
--                 SPrin p
--                 -> SPrin q
--                 -> c m e n (Δ p) (I q) (p ∧ C q) a
--                 -> c m e n (Δ p) (I q) (p ∧ q) a
--nm_six p q v = iassume ((p*←) ≽ (q*←)) (reprotect_b v)
