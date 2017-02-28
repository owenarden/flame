{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.STM
where

import Control.Concurrent.STM as STM (STM, atomically, TVar, newTVar, newTVarIO,
                                           readTVar, readTVarIO, writeTVar, modifyTVar) 
import Flame.Principals
import Flame.TCB.IFC 
import Data.IORef

data IFCTVar (l::KPrin) a = IFCTVar { unsafeUnwrap :: TVar a}

atomically :: (IFC m STM n, IFC m IO n) => m STM n pc l a -> m IO n pc l a
atomically t = unsafeProtect $ STM.atomically $ runIFC t

newIFCTVar :: (IFC m STM n, pc ⊑ l) => a -> m STM n pc pc (IFCTVar l a)
newIFCTVar a = unsafeProtect $ do 
               r <- STM.newTVar a
               return . label $ IFCTVar r

readIFCTVar :: IFC m STM n => IFCTVar l a -> m STM n pc (pc ⊔ l) a
readIFCTVar ref = unsafeProtect $ do 
                   r <- STM.readTVar (unsafeUnwrap ref)
                   return . label $ r

writeIFCTVar :: (IFC m STM n, pc ⊑ l) => IFCTVar l a -> a -> m STM n pc pc' ()
writeIFCTVar ref a = unsafeProtect $ do 
                      STM.writeTVar (unsafeUnwrap ref) a;
                      return . label $ ()

modifyIFCTVar :: (IFC m STM n, pc ⊑ l) => IFCTVar l a -> (a -> a) -> m STM n pc pc' ()
modifyIFCTVar ref f = unsafeProtect $ do 
                      STM.modifyTVar (unsafeUnwrap ref) f;
                      return . label $ ()

newIFCTVarIO :: (IFC m IO n, pc ⊑ l) => a -> m IO n pc pc (IFCTVar l a)
newIFCTVarIO a = unsafeProtect $ do 
                  r <- STM.newTVarIO a
                  return . label $ IFCTVar r

readIFCTVarIO :: IFC m IO n => IFCTVar l a -> m IO n pc (pc ⊔ l) a
readIFCTVarIO ref = unsafeProtect $ do 
                   r <- STM.readTVarIO (unsafeUnwrap ref)
                   return . label $ r