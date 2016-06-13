{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module Auth where

import Flame.Principals
import Flame.IFC 

handoff :: (pc ≽ Voice (C p), pc ≽ I q) =>
           (Voice (C q) :≽ Voice (C p))
           -> (p :⊑ q)
           -> IFC pc l (IFC pc' p a -> IFC pc' q a)
handoff pf1 pf2 = assume pf1 $ assume pf2 $ protect relabel
