{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE RecordWildCards            #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#if __GLASGOW_HASKELL__ < 801
#define nonDetCmpType cmpType
#endif

module Flame.Solver.Unify
  ( -- * 'Nat' expressions \<-\> 'Norm' terms
    --CType (..)
    -- * Find unifiers
    SolverResult (..)
  , solvePrins
    -- * Free variables in 'Norm' terms
  , fvNorm
  )
where

-- External
import Data.Function (on)
import Data.List     ((\\), intersect, mapAccumL)
import UniqSet       (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                       unitUniqSet)
-- GHC API
import Outputable    (Outputable (..), (<+>), ($$), text, pprTrace)
import TcPluginM     (TcPluginM, tcPluginTrace)
import TcRnMonad     (Ct, ctEvidence, isGiven)
import TcRnTypes     (ctEvPred)
import TcTypeNats    (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                      typeNatSubTyCon)
import Type          (EqRel (NomEq), PredTree (EqPred), TyVar, classifyPredType,
                      coreView, eqType, mkNumLitTy, mkTyConApp, mkTyVarTy,
                      nonDetCmpType)
import TyCoRep       (Type (..), TyLit (..))

import Flame.Solver.Data
import Flame.Solver.Norm
import Flame.Solver.ActsFor

---- | A substitution is essentially a list of (variable, 'Norm') pairs,
---- but we keep the original 'Ct' that lead to the substitution being
---- made, for use when turning the substitution back into constraints.
--type CoreUnify = UnifyItem TyVar Type
--
---- | Result of comparing two 'Norm' terms, returning a potential substitution
---- list under which the two terms are equal.
data SolverResult
  = Win                           -- ^ Two terms are equal
  | Lose                          -- ^ Two terms are /not/ equal
  | Draw (CoreBounds, CoreBounds) -- ^ Two terms are only equal if the given substitution holds
--
--instance Outputable UnifyResult where
--  ppr Win          = text "Win"
--  ppr (Draw subst) = text "Draw" <+> ppr subst
--  ppr Lose         = text "Lose"

-- | Given two 'Norm's @u@ and @v@, when their free variables ('fvNorm') are the
-- same, then we 'Win' if @u@ and @v@ are equal, and 'Lose' otherwise.
--
-- If @u@ and @v@ do not have the same free variables, we result in a 'Draw',
-- ware @u@ and @v@ are only equal when the returned 'CoreSubst' holds.
solvePrins :: FlameRec -> Ct -> CoreNorm -> CoreNorm -> TcPluginM SolverResult
solvePrins flrec ct u v = do
  tcPluginTrace "solvePrins" (ppr ct $$ ppr u $$ ppr v)
  return (solvePrins' flrec ct u v)

solvePrins' :: FlameRec -> Ct -> CoreNorm -> CoreNorm -> SolverResult
solvePrins' flrec ct u v
  = case actsFor flrec u v of
      Just pf -> Win
      Nothing -> Lose
        --Draw (confBounds flrec, integBounds flrec)
  --where
  --  -- A unifier is only a unifier if differs from the original constraint
  --  diffFromConstraint (UnifyItem x y) = not (x == u && y == v)
  --  diffFromConstraint _               = True

---- | Find unifiers for two Norm terms
--unifiers :: FlameRec -> Ct -> CoreNorm -> CoreNorm -> [CoreUnify]
--unifiers flrec ct (N cp ip) (N cq iq) =
--  case (p, q) of
--    (p@(N cp ip), q@(N cq (J [M [V v]]))) -> [SubstItem v (sub v bot)]
--    (p@(J [M [V v]]), q) -> [SubstItem v (sub v q)]
--    _ -> []
-- where
--   bot = (J [M [B]]) 
--   isub v p = (N (J [M [V v]]) p)
--   csub v p = (N p (J [M [V v]]))
--   sub v p = if isConf then csub v p else isub v p
--  (unifiers' flrec ct True cp cq) ++  (unifiers' flrec ct False ip iq)
--
--unifiers' :: FlameRec -> Ct -> Bool -> CoreJNorm -> CoreJNorm -> [CoreUnify]
--unifiers' flrec _ct isConf p q =
--  case (p, q) of
--    (p, q@(J [M [V v]])) -> [SubstItem v (sub v bot)]
--    (p@(J [M [V v]]), q) -> [SubstItem v (sub v q)]
--    _ -> []
-- where
--   bot = (J [M [B]]) 
--   isub v p = (N (J [M [V v]]) p)
--   csub v p = (N p (J [M [V v]]))
--   sub v p = if isConf then csub v p else isub v p

--containsConstants :: CoreNorm -> Bool
--containsConstants (N c_u i_u) = containsConstants' c_u || containsConstants' i_u 
--  where
--    containsConstants' = any (any (\c -> case c of
--                                 {(P _) -> True; B -> True; T -> True; _ -> False}) . unM) . unJ

{- | Collect the free variables of a normalized principal -}
fvNorm :: CoreNorm -> UniqSet TyVar
fvNorm (N conf integ) = fvJNorm conf `unionUniqSets` fvJNorm integ

-- | Find the 'TyVar' in a 'CoreJNorm'
fvJNorm :: CoreJNorm -> UniqSet TyVar
fvJNorm = unionManyUniqSets . map fvMNorm . unJ

fvMNorm :: CoreMNorm -> UniqSet TyVar
fvMNorm = unionManyUniqSets . map fvBase . unM

fvBase :: CoreBase -> UniqSet TyVar
fvBase (P _)   = emptyUniqSet
fvBase B   = emptyUniqSet
fvBase T   = emptyUniqSet
fvBase (V v)   = unitUniqSet v
fvBase (VarVoice v)   = unitUniqSet v
fvBase (VarEye v)   = unitUniqSet v

eqFV :: CoreNorm -> CoreNorm -> Bool
eqFV = (==) `on` fvNorm
