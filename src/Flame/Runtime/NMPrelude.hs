{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Flame.Runtime.NMPrelude
  ( 
    module Prelude
  , module Flame.Principals
  , module Flame.Runtime.Principals
  , module Flame.Runtime.NMIO
  , module Flame.TCB.NMIFC
  , return, (>>=), (>>), ifThenElse
  )
 where

import Flame.Principals
import Flame.Runtime.Principals
import Flame.Runtime.NMIO
import Flame.TCB.NMIFC 

import Prelude hiding ( return, (>>=), (>>)
                      , print, putStr, putStrLn, getLine)

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ f = f

return :: NMFLA m n => a -> m n β pc l a
return = protect

(>>=) :: (NMFLA m n, l ⊑ l', (pc ⊔ l) ⊑ pc', l ⊑ β', β' ⊑ β)
         => m n β pc l a
         -> (a -> m n β' pc' l' b)
         -> m n β' pc' l' b
(>>=) = use

(>>) :: (NMFLA m n, pc ⊑ pc', β' ⊑ β)
         => m n β pc l a
         -> m n β' pc' l' b
         -> m n β' pc' l' b
m >> a = apply m $ \_ -> a
