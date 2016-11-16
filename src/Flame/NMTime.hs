{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.NMTime
       ( getCurrentTime
       , getCurrentTimex
       , module Data.Time
       )
where
import qualified Data.Time as T
import Data.Time hiding (getCurrentTime)
import Flame.Type.Principals
import Flame.Type.TCB.IFC 
import Flame.Type.TCB.NMIFC 

{- | Get the current UTC time from the system clock. -}
getCurrentTime :: NMIFC IO b pc PT UTCTime
getCurrentTime = UnsafeNMIFC $ do t <- T.getCurrentTime
                                  return $ label t

getCurrentTimex :: SPrin b ->  SPrin pc -> NMIFC IO b pc PT UTCTime
getCurrentTimex b pc = getCurrentTime
