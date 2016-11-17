{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Flame.Runtime.Prelude
  ( 
    module Prelude
  , module Flame.Principals
  , module Flame.IFC
  , module Flame.Runtime.Principals
  , module Flame.Runtime.IO
  , return, (>>=), (>>), ifThenElse
  )
 where

import Flame.Principals
import Flame.IFC 
import Flame.Runtime.Principals
import Flame.Runtime.IO

import Prelude hiding ( return, (>>=), (>>)
                      , print, putStr, putStrLn, getLine)

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ f = f

return :: FLA m n => a -> m n pc l a
return = protect

(>>=) :: (FLA m n, l ⊑ l', (pc ⊔ l) ⊑ pc')
         => m n pc l a
         -> (a -> m n pc' l' b)
         -> m n pc' l' b
(>>=) = use

(>>) :: (FLA m n, pc ⊑ pc')
         => m n pc l a
         -> m n pc' l' b
         -> m n pc' l' b
m >> a = apply m $ \_ -> a
