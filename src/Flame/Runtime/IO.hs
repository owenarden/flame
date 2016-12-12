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

hFlush :: forall pc l' m n l. (FLA m IO n, pc ⊑ l) => FLAHandle l -> m IO n pc l' ()
hFlush h = unsafeProtect $ do
  _ <- SIO.hFlush (unsafeUnwrap h)
  return $ label ()

hPrint :: forall pc l' m n l a. (FLA m IO n, Show a, pc ⊑ l) => FLAHandle l -> a -> m IO n pc l' ()
hPrint h s = unsafeProtect $ do
  _ <- SIO.hPrint (unsafeUnwrap h) s
  return $ label ()

hPutChar :: forall pc l' m n l. (FLA m IO n, pc ⊑ l) => FLAHandle l -> Char -> m IO n pc l' ()
hPutChar h c = unsafeProtect $ do
  _ <- SIO.hPutChar (unsafeUnwrap h) c
  return $ label ()

hPutStr :: forall pc l' m n l. (FLA m IO n, pc ⊑ l) => FLAHandle l -> String -> m IO n pc l' ()
hPutStr h s = unsafeProtect $ do
  _ <- SIO.hPutStr (unsafeUnwrap h) s
  return $ label ()

hPutStrLn :: forall pc l' m n l. (FLA m IO n, pc ⊑ l) => FLAHandle l -> String -> m IO n pc l' ()
hPutStrLn h s = unsafeProtect $ do
  _ <- SIO.hPutStrLn (unsafeUnwrap h) s
  return $ label ()

hGetChar :: forall pc l m n. FLA m IO n => FLAHandle l -> m IO n pc l Char
hGetChar h = unsafeProtect $ do
  c <- SIO.hGetChar (unsafeUnwrap h)
  return $ label c

hGetLine :: forall pc l m n. FLA m IO n => FLAHandle l -> m IO n pc l String
hGetLine h = unsafeProtect $ do
  s <- SIO.hGetLine (unsafeUnwrap h)
  return $ label s
