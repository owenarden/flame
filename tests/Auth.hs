{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module Auth where

import Flame.Type.Principals
import Flame.Type.IFC 

mkCapability :: (Monad e, pc ≽ Voice (C p), pc ≽ I q) =>
           (Voice (C q) :≽ Voice (C p))
           -> (p :⊑ q)
           -> IFC e pc l (IFC e pc' p a -> IFC e pc' q a)
mkCapability pf1 pf2 = assume pf1 $ assume pf2 $ protect relabel
