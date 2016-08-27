{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.Time
       ( getCurrentTime
       , getCurrentTimex
       , module Data.Time
       )
where
import qualified Data.Time as T
import Data.Time hiding (getCurrentTime)
import Flame.Type.Principals
import Flame.Type.TCB.IFC 

{- | Get the current UTC time from the system clock. -}
getCurrentTime :: IFC IO pc PT UTCTime
getCurrentTime = UnsafeIFC $ do t <- T.getCurrentTime
                                return $ label t

getCurrentTimex :: SPrin pc -> IFC IO pc PT UTCTime
getCurrentTimex pc = getCurrentTime
