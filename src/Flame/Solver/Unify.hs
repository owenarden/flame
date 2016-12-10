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
    -- * Substitution on 'Norm' terms
    UnifyItem (..)
  , CoreUnify
  , substsNorm
  , substsSubst
    -- * Find unifiers
  , UnifyResult (..)
  , unifyPrins
  , unifiers
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
import Outputable    (Outputable (..), (<+>), ($$), text)
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

-- | A substitution is essentially a list of (variable, 'Norm') pairs,
-- but we keep the original 'Ct' that lead to the substitution being
-- made, for use when turning the substitution back into constraints.
type CoreUnify = UnifyItem TyVar Type

data UnifyItem v c = SubstItem { siVar  :: v
                               , siNorm  :: Norm v c
                               }
                   | UnifyItem { siLHS  :: Norm v c
                               , siRHS  :: Norm v c
                               }

instance (Outputable v, Outputable c) => Outputable (UnifyItem v c) where
  ppr (SubstItem {..}) = ppr siVar <+> text " := " <+> ppr siNorm
  ppr (UnifyItem {..}) = ppr siLHS <+> text " :~ " <+> ppr siRHS

-- | Apply a substitution to a single normalised 'Norm' term
substsNorm :: (Ord v, Ord c) => [UnifyItem v c] -> Norm v c -> Norm v c
substsNorm []                   u = u
substsNorm ((SubstItem {..}):s) u = substsNorm s (substNorm siVar siNorm u)
substsNorm ((UnifyItem {}):s)   u = substsNorm s u

substNorm :: (Ord v, Ord c) => v -> Norm v c -> Norm v c -> Norm v c
substNorm tv sub (N c_u i_u) = N (substJNorm True tv sub c_u)
                                 (substJNorm False tv sub i_u)

substJNorm :: (Ord v, Ord c) => Bool -> v -> Norm v c -> JNorm v c -> JNorm v c
substJNorm isConf tv e = foldr1 mergeJNormJoin . map (substMNorm isConf tv e) . unJ

substMNorm :: (Ord v, Ord c) => Bool -> v -> Norm v c -> MNorm v c -> JNorm v c
substMNorm isConf tv e = foldr1 mergeJNormMeet . map (substBase isConf tv e) . unM

substBase :: (Ord v, Ord c) => Bool -> v -> Norm v c -> Base v c -> JNorm v c
substBase _ _ _ B = J [M [B]]
substBase _ _ _ T = J [M [T]]
substBase _ _ _ p@(P s) = J [M [p]]
substBase isConf tv (N c_u i_u) (V tv')
  | tv == tv'            = if isConf then c_u else i_u
  | otherwise            = J [M [V tv']]
substBase isConf tv u (VarVoice tv')
  | tv == tv'            = if isConf then
                             J [M [B]] -- XXX: should have already been removed
                           else
                             integ (voiceOf u)
  | otherwise            = J [M [VarVoice tv']]
substBase isConf tv u (VarEye tv')
  | tv == tv'            = if isConf then
                             conf (eyeOf u)
                           else
                             J [M [B]] -- XXX: should have already been removed
  | otherwise            = J [M [VarEye tv']]

-- | Apply a substitution to a substitution
substsSubst :: (Ord v, Ord c) => [UnifyItem v c] -> [UnifyItem v c] -> [UnifyItem v c]
substsSubst s = map subt
  where
    subt si@(SubstItem {..}) = si {siNorm = substsNorm s siNorm}
    subt si@(UnifyItem {..}) = si {siLHS = substsNorm s siLHS, siRHS = substsNorm s siRHS}
{-# INLINEABLE substsSubst #-}

-- | Result of comparing two 'Norm' terms, returning a potential substitution
-- list under which the two terms are equal.
data UnifyResult
  = Win              -- ^ Two terms are equal
  | Lose             -- ^ Two terms are /not/ equal
  | Draw [CoreUnify] -- ^ Two terms are only equal if the given substitution holds

instance Outputable UnifyResult where
  ppr Win          = text "Win"
  ppr (Draw subst) = text "Draw" <+> ppr subst
  ppr Lose         = text "Lose"

-- | Given two 'Norm's @u@ and @v@, when their free variables ('fvNorm') are the
-- same, then we 'Win' if @u@ and @v@ are equal, and 'Lose' otherwise.
--
-- If @u@ and @v@ do not have the same free variables, we result in a 'Draw',
-- ware @u@ and @v@ are only equal when the returned 'CoreSubst' holds.
unifyPrins :: Ct -> CoreNorm -> CoreNorm -> TcPluginM UnifyResult
unifyPrins ct u v = do
  tcPluginTrace "unifyPrins" (ppr ct $$ ppr u $$ ppr v)
  return (unifyPrins' ct u v)

unifyPrins' :: Ct -> CoreNorm -> CoreNorm -> UnifyResult
unifyPrins' ct u v
  = if eqFV u v
       then if containsConstants u || containsConstants v
               then if u == v
                       then Win
                       else Draw (filter diffFromConstraint (unifiers ct u v))
               else if u == v
                       then Win
                       else Lose
       else Draw (filter diffFromConstraint (unifiers ct u v))
  where
    -- A unifier is only a unifier if differs from the original constraint
    diffFromConstraint (UnifyItem x y) = not (x == u && y == v)
    diffFromConstraint _               = True

-- | Find unifiers for two Norm terms
unifiers :: Ct -> CoreNorm -> CoreNorm -> [CoreUnify]
unifiers _ct s1 s2               = []

containsConstants :: CoreNorm -> Bool
containsConstants (N c_u i_u) = containsConstants' c_u || containsConstants' i_u 
  where
    containsConstants' = any (any (\c -> case c of
                                 {(P _) -> True; B -> True; T -> True; _ -> False}) . unM) . unJ

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
