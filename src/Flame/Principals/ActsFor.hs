module Flame.Principals.ActsFor
where
import Flame.Principals.Dynamic

-- External
import Control.Arrow       ((***))
import Data.Maybe          (mapMaybe)
import Data.Either (partitionEithers)
import Data.List   (partition, sort, find, group)
import Data.Graph 

type DelClosure = [(Base, [Base])]

actsFor :: DelClosure -- ^ [G]iven conf delegations
           -> DelClosure -- ^ [G]iven integ delegations
           -> (Prin , Prin)
           -> Maybe ActsForProof
actsFor confClosure integClosure (Top, q) = Just AFTop
actsFor confClosure integClosure (p , Bot) = Just AFBot
actsFor confClosure integClosure (p,q)
  | p == q    = Just AFRefl
  | otherwise = --pprTrace "actsFor" (ppr (p,q)) $
        let p' = normPrin p in
        let q' = normPrin q in do
          confPf <- confActsFor (conf p', conf q')
          integPf <- integActsFor (integ p', integ q')
          Just $ AFConj [confPf, integPf]
  where
    top :: Norm
    top = N (J [M [T]]) (J [M [T]])
    bot :: Norm
    bot = N (J [M [B]]) (J [M [B]])

    confActsFor :: (JNorm, JNorm) -> Maybe ActsForProof
    confActsFor = actsForJ confClosure 
    integActsFor :: (JNorm, JNorm) -> Maybe ActsForProof
    integActsFor = actsForJ integClosure

actsForJ :: DelClosure ->
            (JNorm, JNorm) ->
            Maybe ActsForProof
actsForJ delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = --pprTrace "actsForJ" (ppr (p,q)) $
                AFConj <$> conjProofs 
  where
    top :: JNorm
    top = J [M [T]]
    bot :: JNorm
    bot = J [M [B]] 
    -- for every join comp on rhs, find sup on lhs
    (J pms, J qms) = (p,q)
    conjProofs :: Maybe [ActsForProof]
    conjProofs = sequence $ map (\qm ->
                                  case mapMaybe (\pm ->
                                                  actsForM delClosure (pm,qm))
                                                pms
                                  of
                                    (pf:pfs) ->
                                      --pprTrace "found proof" (ppr pf) $
                                      Just pf
                                    [] -> Nothing
                                )
                                qms

actsForM :: DelClosure ->
            (MNorm, MNorm) ->
            Maybe ActsForProof
actsForM delClosure (p,q) 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = AFDisj <$> disjProofs
  where
    top :: MNorm
    top = M [T]
    bot :: MNorm
    bot = M [B] 
    -- for every meet comp on lhs, find inf on rhs
    (M pbs, M qbs) = (p,q)
    disjProofs :: Maybe [ActsForProof]
    disjProofs = sequence $ map (\pb ->
                                  case mapMaybe (\qb ->
                                                  actsForB delClosure (pb,qb))
                                                qbs
                                  of
                                    (pf:pfs) -> Just pf
                                    [] -> Nothing
                                )
                                pbs

-- IDEA for transitivity.  If all given dels are expressed "primitively",
-- then transitivity can be exploited as simple reachability via given dels.
actsForB :: DelClosure ->
            (Base, Base) ->
            Maybe ActsForProof
actsForB delClosure (p,q) 
  | p == top = Just AFTop
  | q == bot = Just AFBot
  | p == q  = Just AFRefl
  | otherwise = --pprTrace "actsForB" (ppr (p,q)) $
    case find (== p) (superiors q) of
      Just del -> Just $ AFDel (p,q)
      _ -> Nothing
  where
    top :: Base
    top = T
    bot :: Base
    bot = B  
    superiors :: Base -> [Base]
    superiors q = case find ((== q) . fst) delClosure of
                    Just (q, sups) -> sups
                    _ -> []

computeDelClosures :: [(Prin,Prin)] -> (DelClosure, DelClosure)
computeDelClosures givens =
  let (confGivens, integGivens) = unzip $ map
                        (\(p,q) ->
                          case (normPrin p, normPrin q) of
                            -- TODO: This fails on givens that aren't already in base form
                            (N (J [M [supC]]) (J [M [supI]]), 
                             N (J [M [infC]]) (J [M [infI]])) -> 
                              ((supC, infC), (supI, infI))
                            _ -> error "not in base form" )
                        givens
  in (computeClosure confGivens,  computeClosure integGivens) 
  -- TODO: expand given constraints to "base form": conf or integ, no RHS conj, no LHS disj
  {- TODO:
    - for each conjunction on the LHS, add a pseudo-node to the graph that is
        reachable from each conjunct and from which the intersection of the
        superiors of each conjunct are reachable.
    - for each disjunction on the RHS, add a pseudo-node to the graph that
        reaches the disjunction and is reachable from the intersection of
        the inferiors of each disjunct.
    - fixpoint?
  -}

computeClosure :: [(Base,Base)] -> DelClosure
computeClosure givens = 
    map (\q -> (q, case prinToVtx q of
                   Just vtx -> map vtxToPrin $ reachable graph vtx))
        principals
  where
    principals :: [Base]
    principals = [T, B] ++ (map head . group . sort $ (map inferior givens ++ map superior givens))

    edges :: [(Base, Base, [Base])]
    edges =  map (\inf ->
                   (inf, inf, [superior af | af  <- givens, inferior af == inf]))
                 principals
    (graph, vtxToEdges, prinToVtx) = graphFromEdges edges

    vtxToPrin :: Vertex -> Base
    vtxToPrin v = let (x, _, _) = vtxToEdges v in x

    inferior :: (Base,Base) -> Base
    inferior = snd

    superior :: (Base,Base) -> Base
    superior = fst
