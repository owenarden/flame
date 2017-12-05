{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Imperative commands. These commands can be used with the 'Program' monad,
-- and different command types can be combined using (':+:').
--
-- These commands are general imperative constructs independent of the back end,
-- except for 'C_CMD' which is C-specific.

module Flame.EDSL.CMD
  ( -- * References
    Ref (..)
  , RefCMD (..)
    -- * Control flow
  , Border (..)
  , borderVal
  , borderIncl
  , IxRange
  , ControlCMD (..)
    -- * File handling
  , Handle (..)
  , stdin
  , stdout
  , PrintfArg (..)
  , mapPrintfArg
  , mapPrintfArgM
  , Formattable (..)
  , FileCMD (..)
  ) where

import Control.Monad.Reader
import Data.Array
import Data.Array.IO
import Data.Char (isSpace)
import Data.Int
import Data.IORef
import Data.List
import Data.Typeable
import Data.Word
import System.IO (IOMode (..))
import qualified System.IO as IO
import qualified Text.Printf as Printf

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
import Data.Foldable hiding (sequence_)
import Data.Traversable (Traversable, traverse)
#endif

import Control.Monad.Operational.Higher

import Control.Monads
import Language.Embedded.Expression
import Language.Embedded.Traversal

-- C-specific imports:
import qualified Language.C.Syntax as C
import Language.C.Quote.C
import Language.C.Monad (CGen)
import Language.Embedded.Backend.C.Expression


import Flame.Principals



--------------------------------------------------------------------------------
-- * References
--------------------------------------------------------------------------------

-- | Mutable reference
data Ref (l :: KPrin) a
    = RefComp VarId
    | RefRun (IORef a)
  deriving (Eq, Typeable)

instance ToIdent (Ref l a) where toIdent (RefComp r) = C.Id r
{-
newIFCRef :: (IFC m IO n, pc ⊑ l) => SPrin l -> a -> m IO n pc pc (IFCRef l a)
newIFCRef l a = unsafeProtect $ do 
                  r <- newIORef a
                  return . label $ IFCRef r

writeIFCRef :: (IFC m IO n, pc ⊑ l) => IFCRef l a -> a -> m IO n pc pc' ()
writeIFCRef ref a = unsafeProtect $ do 
                      writeIORef (unsafeUnwrap ref) a;
                      return . label $ ()

readIFCRef :: IFC m IO n => IFCRef l a -> m IO n pc (pc ⊔ l) a
readIFCRef ref = unsafeProtect $ do 
                   r <- readIORef (unsafeUnwrap ref)
                   return . label $ r
-}
-- | Commands for mutable references
data RefCMD fs a
  where
    NewRef  :: (pred a, pc ⊑ l) => String -> RefCMD (Param4 prog exp pred pc) (Ref l a)
    InitRef :: (pred a, pc ⊑ l) => String -> exp a -> RefCMD (Param4 prog exp pred pc) (Ref l a)
    GetRef  :: (pred a, l ⊑ pc) => Ref l a -> RefCMD (Param4 prog exp pred pc) (Val a)
    SetRef  :: (pred a, pc ⊑ l) => Ref l a -> exp a -> RefCMD (Param4 prog exp pred pc) ()
      -- `pred a` for `SetRef` is not needed for code generation, but it can be
      -- useful when interpreting with a dynamically typed store. It can then be
      -- used e.g. to supply a `Typeable` constraint for casting.
    UnsafeFreezeRef :: (pred a, l ⊑ pc) => Ref l a -> RefCMD (Param4 prog exp pred pc) (Val a)
      -- Like `GetRef` but without using a fresh variable for the result. This
      -- is only safe if the reference is never written to after the freezing.
#if  __GLASGOW_HASKELL__>=708
  deriving Typeable
#endif

instance HFunctor RefCMD
  where
    hfmap _ (NewRef base)       = NewRef base
    hfmap _ (InitRef base a)    = InitRef base a
    hfmap _ (GetRef r)          = GetRef r
    hfmap _ (SetRef r a)        = SetRef r a
    hfmap _ (UnsafeFreezeRef r) = UnsafeFreezeRef r

instance HBifunctor RefCMD
  where
    hbimap _ _ (NewRef base)       = NewRef base
    hbimap _ f (InitRef base a)    = InitRef base (f a)
    hbimap _ _ (GetRef r)          = GetRef r
    hbimap _ f (SetRef r a)        = SetRef r (f a)
    hbimap _ _ (UnsafeFreezeRef r) = UnsafeFreezeRef r

instance (RefCMD :<: instr) => Reexpressible RefCMD instr env
  where
    reexpressInstrEnv reexp (NewRef base)       = lift $ singleInj $ NewRef base
    reexpressInstrEnv reexp (InitRef base a)    = lift . singleInj . InitRef base =<< reexp a
    reexpressInstrEnv reexp (GetRef r)          = lift $ singleInj $ GetRef r
    reexpressInstrEnv reexp (SetRef r a)        = lift . singleInj . SetRef r =<< reexp a
    reexpressInstrEnv reexp (UnsafeFreezeRef r) = lift $ singleInj $ UnsafeFreezeRef r

instance DryInterp RefCMD
  where
    dryInterp (NewRef base)    = liftM RefComp $ freshStr base
    dryInterp (InitRef base _) = liftM RefComp $ freshStr base
    dryInterp (GetRef _)       = liftM ValComp $ freshStr "v"
    dryInterp (SetRef _ _)     = return ()
    dryInterp (UnsafeFreezeRef (RefComp v)) = return $ ValComp v



--------------------------------------------------------------------------------
-- * Arrays (TODO)
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * Control flow
--------------------------------------------------------------------------------

data Border i = Incl i | Excl i
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | 'fromInteger' gives an inclusive border. No other methods defined.
instance Num i => Num (Border i)
  where
    fromInteger = Incl . fromInteger
    (+) = error "(+) not defined for Border"
    (-) = error "(-) not defined for Border"
    (*) = error "(*) not defined for Border"
    abs    = error "abs not defined for Border"
    signum = error "signum not defined for Border"

borderVal :: Border i -> i
borderVal (Incl i) = i
borderVal (Excl i) = i

borderIncl :: Border i -> Bool
borderIncl (Incl _) = True
borderIncl _        = False

-- | Index range
--
-- @(lo,step,hi)@
--
-- @lo@ gives the start index; @step@ gives the step length; @hi@ gives the stop
-- index which may be inclusive or exclusive.
type IxRange i = (i, Int, Border i)

data ControlCMD fs a
  where
    If     :: exp Bool -> prog () -> prog () -> ControlCMD (Param4 prog exp pred pc) ()
    While  :: prog (exp Bool) -> prog () -> ControlCMD (Param4 prog exp pred pc) ()
    For    :: (pred i, Integral i) => IxRange (exp i) -> (Val i -> prog ()) -> ControlCMD (Param4 prog exp pred pc) ()
    Break  :: ControlCMD (Param4 prog exp pred pc) ()
    Assert :: exp Bool -> String -> ControlCMD (Param4 prog exp pred pc) ()

instance HFunctor ControlCMD
  where
    hfmap f (If c thn els)    = If c (f thn) (f els)
    hfmap f (While cont body) = While (f cont) (f body)
    hfmap f (For rng body)    = For rng (f . body)
    hfmap _ Break             = Break
    hfmap _ (Assert cond msg) = Assert cond msg

instance HBifunctor ControlCMD
  where
    hbimap f g (If c thn els)          = If (g c) (f thn) (f els)
    hbimap f g (While cont body)       = While (f $ fmap g cont) (f body)
    hbimap f g (For (lo,step,hi) body) = For (g lo, step, fmap g hi) (f . body)
    hbimap _ _ Break                   = Break
    hbimap _ g (Assert cond msg)       = Assert (g cond) msg

instance (ControlCMD :<: instr) => Reexpressible ControlCMD instr env
  where
    reexpressInstrEnv reexp (If c thn els) = do
        c' <- reexp c
        ReaderT $ \env ->
          singleInj $ If c' (runReaderT thn env) (runReaderT els env)
    reexpressInstrEnv reexp (While cont body) = ReaderT $ \env ->
        singleInj $ While
            (runReaderT (cont >>= reexp) env)
            (runReaderT body env)
    reexpressInstrEnv reexp (For (lo,step,hi) body) = do
        lo' <- reexp lo
        hi' <- traverse reexp hi
        ReaderT $ \env -> singleInj $
            For (lo',step,hi') (flip runReaderT env . body)
    reexpressInstrEnv reexp Break             = lift $ singleInj Break
    reexpressInstrEnv reexp (Assert cond msg) = lift . singleInj . flip Assert msg =<< reexp cond

instance DryInterp ControlCMD
  where
    dryInterp (If _ _ _)   = return ()
    dryInterp (While _ _)  = return ()
    dryInterp (For _ _)    = return ()
    dryInterp Break        = return ()
    dryInterp (Assert _ _) = return ()



--------------------------------------------------------------------------------
-- * Generic pointer manipulation
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * File handling
--------------------------------------------------------------------------------

-- | File handle
data Handle (l::KPrin)
    = HandleComp VarId
    | HandleRun IO.Handle
  deriving (Eq, Show, Typeable)

instance ToIdent (Handle l) where toIdent (HandleComp h) = C.Id h

-- | Handle to stdin
stdin :: Handle KBot
stdin = HandleComp "stdin"

-- | Handle to stdout
stdout :: Handle KBot
stdout = HandleComp "stdout"

data PrintfArg exp
  where
    PrintfArg :: Printf.PrintfArg a => exp a -> PrintfArg exp

mapPrintfArg :: (forall a . exp1 a -> exp2 a)
    -> PrintfArg exp1 -> PrintfArg exp2
mapPrintfArg f (PrintfArg exp) = PrintfArg (f exp)

mapPrintfArgM :: Monad m
    => (forall a . exp1 a -> m (exp2 a))
    -> PrintfArg exp1 -> m (PrintfArg exp2)
mapPrintfArgM f (PrintfArg exp) = liftM PrintfArg (f exp)

-- | Values that can be printed\/scanned using @printf@\/@scanf@
class (Typeable a, Read a, Printf.PrintfArg a) => Formattable a
  where
    -- | Format specifier for `printf`
    formatSpecPrint :: Proxy a -> String
    -- | Format specifier for `scanf`
    formatSpecScan  :: Proxy a -> String
    formatSpecScan = formatSpecPrint

instance Formattable Int    where formatSpecPrint _ = "%d"
instance Formattable Int8   where formatSpecPrint _ = "%hhd"
instance Formattable Int16  where formatSpecPrint _ = "%hd"
instance Formattable Int32  where formatSpecPrint _ = "%d"
instance Formattable Int64  where formatSpecPrint _ = "%ld"
instance Formattable Word   where formatSpecPrint _ = "%u"
instance Formattable Word8  where formatSpecPrint _ = "%hhu"
instance Formattable Word16 where formatSpecPrint _ = "%hu"
instance Formattable Word32 where formatSpecPrint _ = "%u"
instance Formattable Word64 where formatSpecPrint _ = "%lu"

instance Formattable Float
  where
    formatSpecPrint _ = "%.9g"
      -- See <http://stackoverflow.com/a/21162120/1105347>
    formatSpecScan _ = "%g"

instance Formattable Double
  where
    formatSpecPrint _ = "%.17g"
      -- See <http://stackoverflow.com/a/21162120/1105347>
    formatSpecScan _ = "%lg"
      -- See <http://stackoverflow.com/q/210590/1105347>

data FileCMD fs a
  where
    FOpen   :: (pc ⊑ l) => {- DPrin l -> -} FilePath -> IOMode -> FileCMD (Param4 prog exp pred pc) (Handle l)
    FClose  :: (pc ⊑ l) => Handle l             -> FileCMD (Param4 prog exp pred pc) ()
    FEof    :: (l ⊑ pc) => Handle l -> FileCMD (Param4 prog exp pred pc) (Val Bool)
    FPrintf :: (pc ⊑ l) => Handle l -> String -> [PrintfArg exp] -> FileCMD (Param4 prog exp pred pc) ()
    FGet    :: (pred a, Formattable a, l ⊑ pc) => Handle l  -> FileCMD (Param4 prog exp pred pc) (Val a)

instance HFunctor FileCMD
  where
    hfmap _ (FOpen file mode)     = FOpen file mode
    hfmap _ (FClose hdl)          = FClose hdl
    hfmap _ (FPrintf hdl form as) = FPrintf hdl form as
    hfmap _ (FGet hdl)            = FGet hdl
    hfmap _ (FEof hdl)            = FEof hdl

instance HBifunctor FileCMD
  where
    hbimap _ _ (FOpen file mode)     = FOpen file mode
    hbimap _ _ (FClose hdl)          = FClose hdl
    hbimap _ f (FPrintf hdl form as) = FPrintf hdl form (map (mapPrintfArg f) as)
    hbimap _ _ (FGet hdl)            = FGet hdl
    hbimap _ _ (FEof hdl)            = FEof hdl

instance (FileCMD :<: instr) => Reexpressible FileCMD instr env
  where
    reexpressInstrEnv reexp (FOpen file mode)   = lift $ singleInj $ FOpen file mode
    reexpressInstrEnv reexp (FClose h)          = lift $ singleInj $ FClose h
    reexpressInstrEnv reexp (FEof h)            = lift $ singleInj $ FEof h
    reexpressInstrEnv reexp (FPrintf h form as) = lift . singleInj . FPrintf h form =<< mapM (mapPrintfArgM reexp) as
    reexpressInstrEnv reexp (FGet h)            = lift $ singleInj $ FGet h

instance DryInterp FileCMD
  where
    dryInterp (FOpen _ _)     = liftM HandleComp $ freshStr "h"
    dryInterp (FClose _)      = return ()
    dryInterp (FPrintf _ _ _) = return ()
    dryInterp (FGet _)        = liftM ValComp $ freshStr "v"
    dryInterp (FEof _)        = liftM ValComp $ freshStr "v"



--------------------------------------------------------------------------------
-- * C-specific commands
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * Running commands
--------------------------------------------------------------------------------

runRefCMD :: RefCMD (Param4 IO IO pred pc) a -> IO a
runRefCMD (NewRef _)              = fmap RefRun $ newIORef $ error "reading uninitialized reference"
runRefCMD (InitRef _ a)           = fmap RefRun . newIORef =<< a
runRefCMD (SetRef (RefRun r) a)   = writeIORef r =<< a
runRefCMD (GetRef (RefRun r))     = ValRun <$> readIORef r
runRefCMD cmd@(UnsafeFreezeRef r) = runRefCMD (GetRef r `asTypeOf` cmd)

runControlCMD :: ControlCMD (Param4 IO IO pred pc) a -> IO a
runControlCMD (If c t f)        = c >>= \c' -> if c' then t else f
runControlCMD (While cont body) = loop
  where loop = do
          c <- join cont
          when c (body >> loop)
runControlCMD (For (lo,step,hi) body) = do
    lo' <- lo
    hi' <- borderVal hi
    loop lo' hi'
  where
    incl = borderIncl hi
    cont i h
      | incl && (step>=0) = i <= h
      | incl && (step<0)  = i >= h
      | step >= 0         = i <  h
      | step < 0          = i >  h
    loop i h
      | cont i h  = body (ValRun i) >> loop (i + fromIntegral step) h
      | otherwise = return ()
runControlCMD Break = error "cannot run programs involving break"
runControlCMD (Assert cond msg) = do
    cond' <- cond
    unless cond' $ error $ "Assertion failed: " ++ msg

{- Unsafe -}
runHandle :: Handle l -> IO.Handle
runHandle (HandleRun h)         = h
runHandle (HandleComp "stdin")  = IO.stdin
runHandle (HandleComp "stdout") = IO.stdout

readWord :: IO.Handle -> IO String
readWord h = do
    eof <- IO.hIsEOF h
    if eof
    then return ""
    else do
      c  <- IO.hGetChar h
      if isSpace c
      then return ""
      else do
        cs <- readWord h
        return (c:cs)

runFPrintf :: [PrintfArg IO] -> (forall r . Printf.HPrintfType r => r) -> IO ()
runFPrintf []               pf = pf
runFPrintf (PrintfArg a:as) pf = a >>= \a' -> runFPrintf as (pf a')

runFileCMD :: FileCMD (Param4 IO IO pred pc) a -> IO a
runFileCMD (FOpen file mode)              = HandleRun <$> IO.openFile file mode
runFileCMD (FClose (HandleRun h))         = IO.hClose h
runFileCMD (FClose (HandleComp "stdin"))  = return ()
runFileCMD (FClose (HandleComp "stdout")) = return ()
runFileCMD (FPrintf h format as)          = runFPrintf as (Printf.hPrintf (runHandle h) format)
runFileCMD (FGet h)   = do
    w <- readWord $ runHandle h
    case reads w of
        [(f,"")] -> return $ ValRun f
        _        -> error $ "fget: no parse (input " ++ show w ++ ")"
runFileCMD (FEof h) = fmap ValRun $ IO.hIsEOF $ runHandle h

instance InterpBi RefCMD     IO (Param2 pred pc) where interpBi = runRefCMD
instance InterpBi ControlCMD IO (Param2 pred pc) where interpBi = runControlCMD
instance InterpBi FileCMD    IO (Param2 pred pc) where interpBi = runFileCMD