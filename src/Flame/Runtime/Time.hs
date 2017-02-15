{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.Time
       ( getCurrentTime
       , module Data.Time
       )
where
import qualified Data.Time as T
import Data.Time hiding (getCurrentTime)
import Flame.Principals
import Flame.TCB.IFC 

{- | Get the current UTC time from the system clock. -}
getCurrentTime :: IFC m IO n => m IO n pc PT UTCTime
getCurrentTime = unsafeProtect $ do t <- T.getCurrentTime
                                    return $ label t
