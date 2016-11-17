{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.Runtime.IFCRef
where

import Flame.Principals
import Flame.TCB.IFC 
import Data.IORef

data IFCRef (l::KPrin) a = IFCRef { unsafeUnwrap :: IORef a}

newIFCRef :: (pc ⊑ l) => SPrin l -> a -> IFC IO pc pc (IFCRef l a)
newIFCRef l a = UnsafeIFC $ do r <- newIORef a
                               return . label $ IFCRef r

newIFCRefx :: (pc ⊑ l) => SPrin pc -> SPrin l -> a -> IFC IO pc pc (IFCRef l a)
newIFCRefx pc = newIFCRef

writeIFCRef :: (pc ⊑ l) => IFCRef l a -> a -> IFC IO pc SU ()
writeIFCRef ref a = UnsafeIFC $ do writeIORef (unsafeUnwrap ref) a;
                                   return . label $ ()

writeIFCRefx :: (pc ⊑ l) => SPrin pc -> IFCRef l a -> a -> IFC IO pc SU ()
writeIFCRefx pc = writeIFCRef

readIFCRef :: IFCRef l a -> IFC IO pc (pc ⊔ l) a
readIFCRef ref = UnsafeIFC $ do r <- readIORef (unsafeUnwrap ref)
                                return . label $ r
readIFCRefx :: SPrin pc -> IFCRef l a -> IFC IO pc (pc ⊔ l) a
readIFCRefx  pc = readIFCRef

--modifyIORef :: IORef a -> (a -> a) -> IO ()
