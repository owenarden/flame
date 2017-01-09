{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.FLARef
where

import Flame.Principals
import Flame.TCB.IFC 
import Data.IORef

data FLARef (l::KPrin) a = FLARef { unsafeUnwrap :: IORef a}

newFLARef :: (FLA m IO n, pc ⊑ l) => SPrin l -> a -> m IO n pc pc (FLARef l a)
newFLARef l a = unsafeProtect $ do 
                  r <- newIORef a
                  return . label $ FLARef r

newFLARef_b :: (BFLA c m IO n, pc ⊑ l) => SPrin l -> a -> c m IO n b pc pc (FLARef l a)
newFLARef_b l a = unsafeBound $ unsafeProtect $ do 
                    r <- newIORef a
                    return . label $ FLARef r

writeFLARef :: (FLA m IO n, pc ⊑ l) => FLARef l a -> a -> m IO n pc pc' ()
writeFLARef ref a = unsafeProtect $ do 
                      writeIORef (unsafeUnwrap ref) a;
                      return . label $ ()

writeFLARef_b :: (BFLA c m IO n, pc ⊑ l) => FLARef l a -> a -> c m IO n b pc pc' ()
writeFLARef_b ref a = unsafeBound $ unsafeProtect $ do 
                        writeIORef (unsafeUnwrap ref) a;
                        return . label $ ()

readFLARef :: FLA m IO n => FLARef l a -> m IO n pc (pc ⊔ l) a
readFLARef ref = unsafeProtect $ do 
                   r <- readIORef (unsafeUnwrap ref)
                   return . label $ r

readFLARef_b :: BFLA c m IO n => FLARef l a -> c m IO n b pc (pc ⊔ l) a
readFLARef_b ref = unsafeBound $ unsafeProtect $ do  
                     r <- readIORef (unsafeUnwrap ref)
                     return . label $ r
--modifyIORef :: IORef a -> (a -> a) -> IO ()
