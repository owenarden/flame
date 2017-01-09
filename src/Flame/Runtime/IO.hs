{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.IO
       {- TODO: interface -}
where
  
import Flame.Principals
import Flame.TCB.IFC 
import qualified System.IO as SIO

data FLAHandle (l::KPrin) = NewHdl { unsafeUnwrap :: SIO.Handle }

mkStdout :: SPrin out -> FLAHandle out
mkStdout out = NewHdl SIO.stdout
mkStderr :: SPrin err -> FLAHandle err
mkStderr err = NewHdl SIO.stderr
mkStdin  :: SPrin in_ -> FLAHandle in_
mkStdin in_ = NewHdl SIO.stdin

hFlush :: (FLA m IO n, pc ⊑ l) => FLAHandle l -> m IO n pc l' ()
hFlush h = unsafeProtect $ do
  _ <- SIO.hFlush (unsafeUnwrap h)
  return $ label ()

hFlush_b :: (BFLA c m IO n, pc ⊑ l) => FLAHandle l -> c m IO n b pc l' ()
hFlush_b h = unsafeBound $ unsafeProtect $ do
  _ <- SIO.hFlush (unsafeUnwrap h)
  return $ label ()

hPrint :: (FLA m IO n, Show a, pc ⊑ l) => FLAHandle l -> a -> m IO n pc l' ()
hPrint h s = unsafeProtect $ do
  _ <- SIO.hPrint (unsafeUnwrap h) s
  return $ label ()

hPrint_b :: (BFLA c m IO n, Show a, pc ⊑ l) => FLAHandle l -> a -> c m IO n b pc l' ()
hPrint_b h s = unsafeBound $ unsafeProtect $ do
  _ <- SIO.hPrint (unsafeUnwrap h) s
  return $ label ()

hPutChar :: (FLA m IO n, pc ⊑ l) => FLAHandle l -> Char -> m IO n pc l' ()
hPutChar h c = unsafeProtect $ do
  _ <- SIO.hPutChar (unsafeUnwrap h) c
  return $ label ()

hPutChar_b :: (BFLA c m IO n, pc ⊑ l) => FLAHandle l -> Char -> c m IO n b pc l' ()
hPutChar_b h c = unsafeBound $ unsafeProtect $ do
  _ <- SIO.hPutChar (unsafeUnwrap h) c
  return $ label ()

hPutStr :: (FLA m IO n, pc ⊑ l) => FLAHandle l -> String -> m IO n pc l' ()
hPutStr h s = unsafeProtect $ do
  _ <- SIO.hPutStr (unsafeUnwrap h) s
  return $ label ()

hPutStr_b :: (BFLA c m IO n, pc ⊑ l) => FLAHandle l -> String -> c m IO n b pc l' ()
hPutStr_b h s = unsafeBound $ unsafeProtect $ do
  _ <- SIO.hPutStr (unsafeUnwrap h) s
  return $ label ()

hPutStrLn :: (FLA m IO n, pc ⊑ l) => FLAHandle l -> String -> m IO n pc l' ()
hPutStrLn h s = unsafeProtect $ do
  _ <- SIO.hPutStrLn (unsafeUnwrap h) s
  return $ label ()

hPutStrLn_b :: (BFLA c m IO n, pc ⊑ l) => FLAHandle l -> String -> c m IO n b pc l' ()
hPutStrLn_b h s = unsafeBound $ unsafeProtect $ do
  _ <- SIO.hPutStrLn (unsafeUnwrap h) s
  return $ label ()

hGetChar :: FLA m IO n => FLAHandle l -> m IO n pc l Char
hGetChar h = unsafeProtect $ do
  c <- SIO.hGetChar (unsafeUnwrap h)
  return $ label c

hGetChar_b :: BFLA c m IO n => FLAHandle l -> c m IO n b pc l Char
hGetChar_b h = unsafeBound $ unsafeProtect $ do
  c <- SIO.hGetChar (unsafeUnwrap h)
  return $ label c

hGetLine :: FLA m IO n => FLAHandle l -> m IO n pc l String
hGetLine h = unsafeProtect $ do
  s <- SIO.hGetLine (unsafeUnwrap h)
  return $ label s

hGetLine_b :: BFLA c m IO n => FLAHandle l -> c m IO n b pc l String
hGetLine_b h = unsafeBound $ unsafeProtect $ do
  s <- SIO.hGetLine (unsafeUnwrap h)
  return $ label s
