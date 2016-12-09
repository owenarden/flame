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

return :: FLA m e n => a -> m e n pc l a
return = protect

(>>=) :: (FLA m e n, l ⊑ l', (pc ⊔ l) ⊑ pc', pc ⊑ pc'')
         => m e n pc l a
         -> (a -> m e n pc' l' b)
         -> m e n pc'' l' b
(>>=) = use

(>>) :: (FLA m e n, pc ⊑ pc', pc ⊑ pc'')
         => m e n pc l a
         -> m e n pc' l' b
         -> m e n pc'' l' b
m >> a = apply m $ \_ -> a
