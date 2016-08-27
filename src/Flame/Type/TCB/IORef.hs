{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.IO
where

import Flame.Type.Principals
import Flame.Type.TCB.IFC 
import Data.IORef

data IFCRef (l::KPrin) a = NewRef { unsafeUnwrap :: IORef a}

newIFCRef :: SPrin l -> a -> IFC IO pc pc (IFCRef l a)
newIFCRef l = UnsafeIFC . NewRef $ newIORef

--newIFCRefx :: SPrin pc -> SPrin l -> a -> IFC IO pc pc (IFCRef l a)
--readIORef :: IORef a -> IO a
--writeIORef :: IORef a -> a -> IO ()
--modifyIORef :: IORef a -> (a -> a) -> IO ()
            
