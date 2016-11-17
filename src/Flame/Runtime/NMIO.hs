{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.NMIO
where
  
import Flame.Principals
import Flame.TCB.NMIFC 
import qualified System.IO as SIO
import Flame.TCB.IFC (Labeled(..), Lbl(..))

data NMIFCHandle (l::KPrin) = NewHdl { unsafeUnwrap :: SIO.Handle }

mkStdout :: SPrin out -> NMIFCHandle out
mkStdout out = NewHdl SIO.stdout
mkStderr :: SPrin err -> NMIFCHandle err
mkStderr err = NewHdl SIO.stderr
mkStdin  :: SPrin in_ -> NMIFCHandle in_
mkStdin in_ = NewHdl SIO.stdin

hFlush :: (pc ⊑ l) => NMIFCHandle l -> NMIFC IO β pc SU ()
hFlush h = UnsafeNMIFC $ do _ <- SIO.hFlush (unsafeUnwrap h)
                            return $ label ()
hFlushx :: (pc ⊑ l) => SPrin β -> SPrin pc -> NMIFCHandle l -> NMIFC IO β pc SU ()
hFlushx b pc = hFlush

hPrint :: (Show a, pc ⊑ l) => NMIFCHandle l -> a -> NMIFC IO β pc SU ()
hPrint h s = UnsafeNMIFC $ do _ <- SIO.hPrint (unsafeUnwrap h) s
                              return $ label ()
hPrintx :: (Show a, pc ⊑ l) => SPrin β -> SPrin pc -> NMIFCHandle l -> a -> NMIFC IO β pc SU ()
hPrintx b pc = hPrint

hPutChar :: (pc ⊑ l) => NMIFCHandle l -> Char -> NMIFC IO β pc SU ()
hPutChar h c = UnsafeNMIFC $ do _ <- SIO.hPutChar (unsafeUnwrap h) c
                                return $ label ()
hPutCharx :: (pc ⊑ l) => SPrin β -> SPrin pc -> NMIFCHandle l -> Char -> NMIFC IO β pc SU ()
hPutCharx b pc = hPutChar

hPutStr :: (pc ⊑ l) => NMIFCHandle l -> String -> NMIFC IO β pc SU ()
hPutStr h s = UnsafeNMIFC $ do _ <- SIO.hPutStr (unsafeUnwrap h) s
                               return $ label ()
hPutStrx :: (pc ⊑ l) => SPrin β -> SPrin pc -> NMIFCHandle l -> String -> NMIFC IO β pc SU ()
hPutStrx b pc = hPutStr

hPutStrLn :: (pc ⊑ l) => NMIFCHandle l -> String -> NMIFC IO β pc SU ()
hPutStrLn h s = UnsafeNMIFC $ do _ <- SIO.hPutStrLn (unsafeUnwrap h) s
                                 return $ label ()
hPutStrLnx :: (pc ⊑ l) => SPrin β -> SPrin pc -> NMIFCHandle l -> String -> NMIFC IO β pc SU ()
hPutStrLnx b pc = hPutStrLn

hGetChar :: NMIFCHandle l -> NMIFC IO β pc l Char
hGetChar h = UnsafeNMIFC $ do c <- SIO.hGetChar (unsafeUnwrap h)
                              return $ label c
hGetCharx :: SPrin β -> SPrin pc -> NMIFCHandle l -> NMIFC IO β pc l Char
hGetCharx b pc = hGetChar

hGetLine :: NMIFCHandle l -> NMIFC IO β pc l String
hGetLine h = UnsafeNMIFC $ do s <- SIO.hGetLine (unsafeUnwrap h)
                              return $ label s
hGetLinex :: SPrin β -> SPrin pc -> NMIFCHandle l -> NMIFC IO β pc l String
hGetLinex b pc = hGetLine
