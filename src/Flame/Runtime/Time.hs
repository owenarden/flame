{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.Time
       ( getCurrentTime
       , getCurrentTime_b
       , module Data.Time
       )
where
import qualified Data.Time as T
import Data.Time hiding (getCurrentTime)
import Flame.Principals
import Flame.TCB.IFC 

{- | Get the current UTC time from the system clock. -}
getCurrentTime :: FLA m IO n => m IO n pc PT UTCTime
getCurrentTime = unsafeProtect $ do t <- T.getCurrentTime
                                    return $ label t

{- | Get the current UTC time from the system clock. -}
getCurrentTime_b :: BFLA c m IO n => c m IO n b pc PT UTCTime
getCurrentTime_b = unsafeBound $ unsafeProtect $ do
                     t <- T.getCurrentTime
                     return $ label t
