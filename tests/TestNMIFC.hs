{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module TestNMIFC where

import Flame.Type.Principals
import Flame.Data.Principals
import Flame.Type.IFC as M
import Flame.Type.TCB.NMIFC as NM

one :: FLA m n => SPrin p -> SPrin q
       -> m n (I q) (C p ∧ (I (p ∨ q))) a
       -> m n (I q) (C p ∧ I q) a
one p q v = assume ((p*←) ≽ (q*←)) (M.reprotect v)

{- #1 -}                             
nm_one :: (NMFLA m n, p ⊑ Δ p) =>
       SPrin p -> SPrin q
       -> m n (Δ p) (I q) (C p ∧ (I (p ∨ q))) a
       -> m n (Δ p) (I q) (C p ∧ I q) a
nm_one p q v = iassume ((p*←) ≽ (q*←)) (NM.reprotect (SEye p) v)

two :: FLA m n => SPrin p -> SPrin q
       -> m n (I p) (C p ∧ (I (p ∨ q))) a
       -> m n (I p) p a
two p q v = assume ((q*←) ≽ (p*←)) (M.reprotect v)

{- #2 -}
{- Fails (as desired): "Could not deduce (C (Δ q) ≽ C (C p ∧ I (p ∨ q)))"
nm_two :: (NMFLA m n, q ⊑ Δ q) => SPrin p -> SPrin q
       -> m n (Δ q) (I p) (C p ∧ (I (p ∨ q))) a
       -> m n (Δ q) (I p) p a
nm_two p q v = iassume ((q*←) ≽ (p*←)) (NM.reprotect (SEye q) v)
-}

three :: FLA m n => SPrin p -> SPrin q
       -> m n ((∇) q) (C (p ∧ q) ∧ (I q)) a
       -> m n ((∇) q) (C p ∧ I q)  a
three p q v = assume ((*∇) (p) ≽ (*∇) (q)) $
                assume ((p*→) ≽ (q*→)) (M.reprotect v)

{- #3 -}
nm_three :: (NMFLA m n, p ~ N p', q ~ N q') => SPrin p -> SPrin q
       -> m n (Δ ((∇) p) ∧ I q) ((∇) q) (C (p ∧ q) ∧ I q) a
       -> m n (Δ ((∇) p) ∧ I q) ((∇) q) (C p ∧ I q) a
nm_three p q v = vassume ((*∇) (p) ≽ ((*∇) (q))) $
                  cassume ((p*→) ≽ (q*→)) (NM.reprotect (SEye (SVoice p) *∧ (q*←)) v)

four :: FLA m n => SPrin p -> SPrin q
       -> m n ((∇) p) (C (p ∧ q) ∧ (I q)) a
       -> m n ((∇) p) q  a
four p q v = assume ((*∇) (q) ≽ (*∇) (p)) $
                assume ((q*→) ≽ (p*→)) (M.reprotect v)

{- #4 (allowed) google doc says this is insecure 
 -   only types if p and q are primitive..
 - -}
nm_four :: (NMFLA m n, q ⊑ Δ q, p ~ N p', q ~ N q') => SPrin p -> SPrin q
       -> m n (Δ ((∇) q) ∧ I q) ((∇) p) (C (p ∧ q) ∧ I q) a
       -> m n (Δ ((∇) q) ∧ I q) ((∇) p) q a
nm_four p q v = vassume ((*∇) (q) ≽ ((*∇) (p))) $
                  cassume ((q*→) ≽ (p*→)) (NM.reprotect (SEye (SVoice q) *∧ (q*←)) v)

five :: FLA m n => SPrin p 
       -> m n (I p) (C p) a
       -> m n (I p) p  a
five p v = assume (((SBot)*←) ≽ (p*←)) (M.reprotect v)

{- #5 not allowed.  This endorsement is malleable. -}
{-
nm_five :: NMFLA m n => SPrin p 
       -> m n (Δ KBot) (I p) (C p) a
       -> m n (Δ KBot) (I p) p  a
nm_five p v = iassume (((SBot)*←) ≽ (p*←)) (NM.reprotect (SEye SBot) v)
-}
{- #5 Alternative 1: Commit only public data. committing it makes it secret. -}
nm_five' :: NMFLA m n => SPrin p 
       -> m n (Δ KBot) (I p) KBot a
       -> m n (Δ KBot) (I p) p  a
nm_five' p v = iassume (((SBot)*←) ≽ (p*←)) (NM.reprotect (SEye SBot) v)

{- #5 Alternative 2: with higher integrity pc, could declass, then endorse.
   seems a little weird, but this is what explicitly permitting malleability
   looks like, I suppose
NB: this doesn't work yet, but might with some extra reasoning in the solver
nm_five'' :: (NMFLA m n, p ⊑ Δ p) => SPrin p 
       -> m n (Δ p ∧ C p) (I p ∧ ((∇) p)) (C p) a
       -> m n (Δ p ∧ C p) (I p ∧ ((∇) p)) p  a
nm_five'' p v = vassume ((*∇)(SBot*→) ≽ (*∇)(p*→)) $
                 eassume (SEye SBot ≽ SEye p) $
                  cassume ((SBot*→) ≽ (p*→)) $
                   iassume ((SBot*←) ≽ (p*←)) $ (NM.reprotect (SEye p *∧ (p*→)) v)
-}

six :: FLA m n => SPrin p -> SPrin q -> m n (I q) (p ∧ C q) a -> m n (I q) (p ∧ q) a
six p q v = assume (p ≽ (q*←)) (M.reprotect v)
{- #6 this is badreceive from Commitment.hs -}
{- Fails (as desired)
nm_six :: (NMFLA m n, p ⊑ Δ p) =>
                 SPrin p
                 -> SPrin q
                 -> m n (Δ p) (I q) (p ∧ C q) a
                 -> m n (Δ p) (I q) (p ∧ q) a
nm_six p q v = iassume ((p*←) ≽ (q*←)) (NM.reprotect (SEye p) v)
-}

seven :: FLA m n => SPrin p -> SPrin q -> m n (I p) (C p ∧ I q) a -> m n (I p) (p ∧ I q) a
seven p q v = assume (q ≽ (p*←)) (M.reprotect v)
{- #7 this is similar to badreceive -}
{- Fails (as desired)
nm_seven :: (NMFLA m n) =>
                 SPrin p
                 -> SPrin q
                 -> m n (Δ q) (I p) (C p ∧ I q) a
                 -> m n (Δ q) (I p) (p ∧ I q) a
nm_seven p q v = iassume ((q*←) ≽ (p*←)) (NM.reprotect (SEye q) v)
-}

{- #8 this is similar to battleship -}
eight :: FLA m n =>
         SPrin p
      -> SPrin q
      -> m n (I p) (C (p ∨ q) ∧ I q) a
      -> m n (I p) (C (p ∨ q) ∧ I (p ∧ q)) a
eight p q v = assume (q ≽ (p*←)) (M.reprotect v)
nm_eight :: (NMFLA m n, q ⊑ Δ q) =>
                 SPrin p
                 -> SPrin q
                 -> m n (Δ q) (I p) (C (p ∨ q) ∧ I q) a
                 -> m n (Δ q) (I p) (C (p ∨ q) ∧ I (p ∧ q)) a
nm_eight p q v = iassume ((q*←) ≽ (p*←)) (NM.reprotect (SEye q) v)

{- #9 is same as #5 (commit) -}

                                   
{- #10 is open from Commitment.hs -}
ten :: FLA m n => SPrin p -> SPrin q -> m n ((∇) p) (p ∧ (I q)) a -> m n ((∇) p) ((I p) ∧ q) a
ten p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (M.reprotect v)

nm_ten :: (NMFLA m n, p ~ N p', q ~ N q') =>
           SPrin p
           -> SPrin q
           -> m n (C (p ∨ q) ∧ I p ∧ ((∇) q)) ((∇) p) (p ∧ (I q)) a
           -> m n (C (p ∨ q) ∧ I p ∧ ((∇) q)) ((∇) p) ((I p) ∧ q) a
nm_ten p q v = vassume (((*∇) (q)) ≽ ((*∇) p)) $ 
                 cassume ((q*→) ≽ (p*→)) 
                  (NM.reprotect (((p *∨ q)*→) *∧ (p*←) *∧ (*∇) q) v)

{- #11 -}
eleven :: (FLA m n, r ≽ q) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m n ((∇) p) (p ∧ (I q)) a
          -> m n ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
eleven p q r v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (M.reprotect v)

--Broken by cassume integrity constraint                                                                 
nm_eleven :: (NMFLA m n, r ≽ q, p ~ N p', q ~ N q', r ~ N r') =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> m n (C q ∧ I p ∧ I q) ((∇) p) (p ∧ (I q)) a
           -> m n (C q ∧ I p ∧ I q) ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
nm_eleven p q r v = iassume ((((*∇) (q))*←) ≽ (((*∇) (p))*←)) $
                 cassume ((q*→) ≽ (p*→)) (NM.reprotect ((q*→) *∧ (p*←) *∧ (q*←)) v)

{- #12 -}
twelve :: (FLA m n, r ≽ q) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m n ((∇) p) (I p ∧ q) a
          -> m n ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
twelve p q r v = M.reprotect v
nm_twelve :: (NMFLA m n, r ≽ q) =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> m n (C q) ((∇) p) (I p ∧ q) a
           -> m n (C q) ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
nm_twelve p q r v = NM.reprotect (q*→) v

{- #13 -}
thirteen :: (FLA m n, q ⊑ r) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m n pc (I p ∧ q) a
          -> m n pc (I p ∧ r) a
thirteen p q r v = M.reprotect v
nm_thirteen :: (NMFLA m n, q ⊑ r) =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> m n (C q) pc (I p ∧ q) a
           -> m n (C q) pc (I p ∧ r) a
nm_thirteen p q r v = NM.reprotect (q*→) v




--nm_four :: (NMFLA m n, q ⊑ Δ q) => SPrin p -> SPrin q
--       -> m n (Δ ((∇) q)) ((∇) p) (C (p ∧ q) ∧ I q) a
--       -> m n (Δ ((∇) q)) ((∇) p) q a
--nm_receive :: (NMFLA m n, p ⊑ Δ p) =>
--              SPrin p
--              -> SPrin q
--              -> m n (Δ p) (I q) p a
--              -> m n (Δ p) (I q) (p ∧ (I q)) a
--nm_six :: (NMFLA m n, p ⊑ Δ p) =>
--                 SPrin p
--                 -> SPrin q
--                 -> m n (Δ p) (I q) (p ∧ C q) a
--                 -> m n (Δ p) (I q) (p ∧ q) a
--nm_six p q v = iassume ((p*←) ≽ (q*←)) (NM.reprotect (SEye p) v)
