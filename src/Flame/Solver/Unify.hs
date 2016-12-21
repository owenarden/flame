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
  , fvJNorm
  )
where

-- External
import Data.List     ((\\), intersect, mapAccumL)
import UniqSet       (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                       unitUniqSet, uniqSetToList)
import Data.Map.Strict (insert, findWithDefault)

-- GHC API
import Outputable    (Outputable (..), (<+>), ($$), text, pprTrace)
import TcType     (isSkolemTyVar)
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
  = Win                      -- ^ Two terms are equal
  | Lose
  | ChangeBounds [(TyVar, CoreJNorm)] -- ^ Two terms are only equal if the given substitution holds

instance Outputable SolverResult where
  ppr Win          = text "Win"
  ppr (ChangeBounds bnds) = text "ChangeBounds" <+> ppr bnds
  ppr Lose         = text "Lose"

-- | Given two 'Norm's @u@ and @v@, when their free variables ('fvNorm') are the
-- same, then we 'Win' if @u@ and @v@ are equal, and 'Lose' otherwise.
--
-- If @u@ and @v@ do not have the same free variables, we result in a 'Draw',
-- ware @u@ and @v@ are only equal when the returned 'CoreSubst' holds.
solvePrins :: FlameRec -> CoreNorm -> CoreNorm -> TcPluginM (SolverResult, SolverResult)
solvePrins flrec p q = do
  tcPluginTrace "solvePrins" (ppr p $$ ppr q)
  return (solvePrins' flrec p q)

solvePrins' :: FlameRec -> CoreNorm -> CoreNorm -> (SolverResult, SolverResult)
solvePrins' flrec p@(N cp ip) q@(N cq iq) =
    (solve (confBounds flrec) True cp cq, solve (integBounds flrec) False ip iq)
  where
    solve bounds isConf p q =
      case actsForJ flrec isConf p q of
        Just pf -> pprTrace "actsforJ win: " (ppr pf) Win
        Nothing ->
          case uniqSetToList $ fvJNorm p of 
            [] -> pprTrace "Lose: no free variables" (ppr p) $
              Lose
            [var] -> case joinWith q (findWithDefault jbot var bounds) of
                       Just bnd ->
                         pprTrace "ChangeBounds: " ((ppr p) <+> text ">=" <+> (ppr bnd)) $ ChangeBounds [(var, bnd)]
                       Nothing -> pprTrace "Lose: var bound unchanged" (ppr p) $
                         Lose
            vars  -> pprTrace "Lose: punting on multivar equations for now." (ppr p) Lose
    joinWith q bnd = let new_bnd = mergeJNormJoin bnd q
                     in pprTrace "old/new" ((ppr bnd) <+> (ppr new_bnd)) $
                         if new_bnd == bnd then
                           Nothing
                         else
                           Just new_bnd
{- | Collect the free variables of a normalized principal -}
fvNorm :: CoreNorm -> UniqSet TyVar
fvNorm (N conf integ) = fvJNorm conf `unionUniqSets` fvJNorm integ

-- | Find the 'TyVar' in a 'CoreJNorm'
fvJNorm :: CoreJNorm -> UniqSet TyVar
fvJNorm = unionManyUniqSets . map fvMNorm . unJ

fvMNorm :: CoreMNorm -> UniqSet TyVar
fvMNorm = unionManyUniqSets . map fvBase . unM

fvBase :: CoreBase -> UniqSet TyVar
fvBase (P _) = emptyUniqSet
fvBase B     = emptyUniqSet
fvBase T     = emptyUniqSet
fvBase (V v)        = if isSkolemTyVar v then emptyUniqSet else unitUniqSet v
fvBase (VarVoice v) = if isSkolemTyVar v then emptyUniqSet else unitUniqSet v
fvBase (VarEye v)   = if isSkolemTyVar v then emptyUniqSet else unitUniqSet v
