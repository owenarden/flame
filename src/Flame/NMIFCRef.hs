{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.NMIFCRef
where

import Flame.Type.Principals
import Flame.Type.TCB.IFC 
import Flame.Type.TCB.NMIFC 
import Data.IORef

data NMIFCRef (l::KPrin) a = NMIFCRef { unsafeUnwrap :: IORef a}

newNMIFCRef :: (pc ⊑ l) => SPrin l -> a -> NMIFC IO β pc pc (NMIFCRef l a)
newNMIFCRef l a = UnsafeNMIFC $ do r <- newIORef a
                                   return . label $ NMIFCRef r

newNMIFCRefx :: (pc ⊑ l) => SPrin pc -> SPrin l -> a -> NMIFC IO β pc pc (NMIFCRef l a)
newNMIFCRefx pc = newNMIFCRef

writeNMIFCRef :: (pc ⊑ l) => NMIFCRef l a -> a -> NMIFC IO β pc SU ()
writeNMIFCRef ref a = UnsafeNMIFC $ do writeIORef (unsafeUnwrap ref) a;
                                       return . label $ ()

writeNMIFCRefx :: (pc ⊑ l) => SPrin pc -> NMIFCRef l a -> a -> NMIFC IO β pc SU ()
writeNMIFCRefx pc = writeNMIFCRef

readNMIFCRef :: NMIFCRef l a -> NMIFC IO β pc (pc ⊔ l) a
readNMIFCRef ref = UnsafeNMIFC $ do r <- readIORef (unsafeUnwrap ref)
                                    return . label $ r
readNMIFCRefx :: SPrin pc -> NMIFCRef l a -> NMIFC IO β pc (pc ⊔ l) a
readNMIFCRefx  pc = readNMIFCRef

--modifyIORef :: IORef a -> (a -> a) -> IO ()
