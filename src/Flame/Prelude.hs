{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Flame.Prelude
  ( 
    module Prelude
  , module Flame.Type.Principals
  , module Flame.Data.Principals
  , module Flame.Type.IFC
  , module Flame.IO
  , return, (>>=), (>>), ifThenElse
  )
 where

import Flame.Type.Principals
import Flame.Data.Principals
import Flame.IO
import Flame.Type.IFC 

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
