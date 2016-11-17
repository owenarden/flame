{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.Runtime.IO
where
  
import Flame.Principals
import Flame.TCB.IFC 
import qualified System.IO as SIO

data IFCHandle (l::KPrin) = NewHdl { unsafeUnwrap :: SIO.Handle }

mkStdout :: SPrin out -> IFCHandle out
mkStdout out = NewHdl SIO.stdout
mkStderr :: SPrin err -> IFCHandle err
mkStderr err = NewHdl SIO.stderr
mkStdin  :: SPrin in_ -> IFCHandle in_
mkStdin in_ = NewHdl SIO.stdin

hFlush :: (pc ⊑ l) => IFCHandle l -> IFC IO pc SU ()
hFlush h = UnsafeIFC $ do _ <- SIO.hFlush (unsafeUnwrap h)
                          return $ label ()
hFlushx :: (pc ⊑ l) => SPrin pc -> IFCHandle l -> IFC IO pc SU ()
hFlushx pc = hFlush

hPrint :: (Show a, pc ⊑ l) => IFCHandle l -> a -> IFC IO pc SU ()
hPrint h s = UnsafeIFC $ do _ <- SIO.hPrint (unsafeUnwrap h) s
                            return $ label ()
hPrintx :: (Show a, pc ⊑ l) => SPrin pc -> IFCHandle l -> a -> IFC IO pc SU ()
hPrintx pc = hPrint

hPutChar :: (pc ⊑ l) => IFCHandle l -> Char -> IFC IO pc SU ()
hPutChar h c = UnsafeIFC $ do _ <- SIO.hPutChar (unsafeUnwrap h) c
                              return $ label ()
hPutCharx :: (pc ⊑ l) => SPrin pc -> IFCHandle l -> Char -> IFC IO pc SU ()
hPutCharx pc = hPutChar

hPutStr :: (pc ⊑ l) => IFCHandle l -> String -> IFC IO pc SU ()
hPutStr h s = UnsafeIFC $ do _ <- SIO.hPutStr (unsafeUnwrap h) s
                             return $ label ()
hPutStrx :: (pc ⊑ l) => SPrin pc -> IFCHandle l -> String -> IFC IO pc SU ()
hPutStrx pc = hPutStr

hPutStrLn :: (pc ⊑ l) => IFCHandle l -> String -> IFC IO pc SU ()
hPutStrLn h s = UnsafeIFC $ do _ <- SIO.hPutStrLn (unsafeUnwrap h) s
                               return $ label ()
hPutStrLnx :: (pc ⊑ l) => SPrin pc -> IFCHandle l -> String -> IFC IO pc SU ()
hPutStrLnx pc = hPutStrLn

hGetChar :: IFCHandle l -> IFC IO pc l Char
hGetChar h = UnsafeIFC $ do c <- SIO.hGetChar (unsafeUnwrap h)
                            return $ label c
hGetCharx :: SPrin pc -> IFCHandle l -> IFC IO pc l Char
hGetCharx pc = hGetChar

hGetLine :: IFCHandle l -> IFC IO pc l String
hGetLine h = UnsafeIFC $ do s <- SIO.hGetLine (unsafeUnwrap h)
                            return $ label s
hGetLinex :: SPrin pc -> IFCHandle l -> IFC IO pc l String
hGetLinex pc = hGetLine
