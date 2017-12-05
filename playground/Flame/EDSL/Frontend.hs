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
{-# OPTIONS_GHC -fplugin Flame.Solver #-}


-- Front end for imperative programs

module Flame.EDSL.Frontend where

import Prelude hiding (break)
import Flame.Principals
import Flame.EDSL.CMD

import Data.Array.IO
import Data.IORef
import Data.Typeable
import System.IO.Unsafe
import System.IO (IOMode)

import Control.Monad.Operational.Higher
import System.IO.Fake
import Language.Embedded.Expression


--------------------------------------------------------------------------------
-- * References
--------------------------------------------------------------------------------

-- | Create an uninitialized reference
newRef :: (pred a, pc ⊑ l, RefCMD :<: instr) =>
    ProgramT instr (Param3 exp pred pc) m (Ref l a)
newRef = newNamedRef "r"

-- | Create an uninitialized named reference
--
-- The provided base name may be appended with a unique identifier to avoid name
-- collisions.
newNamedRef :: (pred a, pc ⊑ l, RefCMD :<: instr)
    => String  -- ^ Base name
    -> ProgramT instr (Param3 exp pred pc) m (Ref l a)
newNamedRef = singleInj . NewRef

-- | Create an initialized reference
initRef :: (pred a, pc ⊑ l, RefCMD :<: instr)
    => exp a  -- ^ Initial value
    -> ProgramT instr (Param3 exp pred pc) m (Ref l a)
initRef = initNamedRef "r"

-- | Create an initialized named reference
--
-- The provided base name may be appended with a unique identifier to avoid name
-- collisions.
initNamedRef :: (pred a, pc ⊑ l, RefCMD :<: instr)
    => String  -- ^ Base name
    -> exp a   -- ^ Initial value
    -> ProgramT instr (Param3 exp pred pc) m (Ref l a)
initNamedRef base a = singleInj (InitRef base a)

-- | Get the contents of a reference
getRef :: (pred a, l ⊑ pc, FreeExp exp, FreePred exp a, RefCMD :<: instr, Monad m) =>
    Ref l a -> ProgramT instr (Param3 exp pred pc) m (exp a)
getRef = fmap valToExp . singleInj . GetRef

-- | Set the contents of a reference
setRef :: (pred a, pc ⊑ l, RefCMD :<: instr) =>
    Ref l a -> exp a -> ProgramT instr (Param3 exp pred pc) m ()
setRef r = singleInj . SetRef r

-- | Modify the contents of reference
modifyRef :: (pred a, pc ⊑ l, l ⊑ pc, FreeExp exp, FreePred exp a, RefCMD :<: instr, Monad m) =>
    Ref l a -> (exp a -> exp a) -> ProgramT instr (Param3 exp pred pc) m ()
modifyRef r f = setRef r . f =<< unsafeFreezeRef r

-- | Freeze the contents of reference (only safe if the reference is not updated
-- as long as the resulting value is alive)
unsafeFreezeRef
    :: (pred a, l ⊑ pc, FreeExp exp, FreePred exp a, RefCMD :<: instr, Monad m)
    => Ref l a -> ProgramT instr (Param3 exp pred pc) m (exp a)
unsafeFreezeRef = fmap valToExp . singleInj . UnsafeFreezeRef

-- | Read the value of a reference without returning in the monad
--
-- WARNING: Don't use this function unless you really know what you are doing.
-- It is almost always better to use 'unsafeFreezeRef' instead.
--
-- 'veryUnsafeFreezeRef' behaves predictably when doing code generation, but it
-- can give strange results when running in 'IO', as explained here:
--
-- <http://fun-discoveries.blogspot.se/2015/09/strictness-can-fix-non-termination.html>
veryUnsafeFreezeRef :: (FreeExp exp, FreePred exp a) => Ref l a -> exp a
veryUnsafeFreezeRef (RefRun r)  = constExp $! unsafePerformIO $! readIORef r
veryUnsafeFreezeRef (RefComp v) = varExp v



--------------------------------------------------------------------------------
-- * Arrays
--------------------------------------------------------------------------------
-- TODO 
--------------------------------------------------------------------------------
-- * Control flow
--------------------------------------------------------------------------------

-- | Conditional statement
iff :: (ControlCMD :<: instr)
    => exp Bool      -- ^ Condition
    -> ProgramT instr (Param3 exp pred pc) m ()  -- ^ True branch
    -> ProgramT instr (Param3 exp pred pc) m ()  -- ^ False branch
    -> ProgramT instr (Param3 exp pred pc) m ()
iff b t f = singleInj $ If b t f

-- | Conditional statement that returns an expression
ifE
    :: ( pred a
       , FreeExp exp
       , FreePred exp a
       , ControlCMD :<: instr
       , RefCMD     :<: instr
       , Monad m
       )
    => exp Bool         -- ^ Condition
    -> ProgramT instr (Param3 exp pred pc) m (exp a)  -- ^ True branch
    -> ProgramT instr (Param3 exp pred pc) m (exp a)  -- ^ False branch
    -> ProgramT instr (Param3 exp pred pc) m (exp a)
ifE b t f = do
    r <- newRef
    iff b (t >>= setRef r) (f >>= setRef r)
    getRef r

-- | While loop
while :: (ControlCMD :<: instr)
    => ProgramT instr (Param3 exp pred pc) m (exp Bool)  -- ^ Continue condition
    -> ProgramT instr (Param3 exp pred pc) m ()          -- ^ Loop body
    -> ProgramT instr (Param3 exp pred pc) m ()
while b t = singleInj $ While b t

-- | For loop
for
    :: ( FreeExp exp
       , ControlCMD :<: instr
       , Integral n
       , pred n
       , FreePred exp n
       )
    => IxRange (exp n)                                   -- ^ Index range
    -> (exp n -> ProgramT instr (Param3 exp pred pc) m ())  -- ^ Loop body
    -> ProgramT instr (Param3 exp pred pc) m ()
for range body = singleInj $ For range (body . valToExp)

-- | Break out from a loop
break :: (ControlCMD :<: instr) => ProgramT instr (Param3 exp pred pc) m ()
break = singleInj Break

-- | Assertion
assert :: (ControlCMD :<: instr)
    => exp Bool  -- ^ Expression that should be true
    -> String    -- ^ Message in case of failure
    -> ProgramT instr (Param3 exp pred pc) m ()
assert cond msg = singleInj $ Assert cond msg



--------------------------------------------------------------------------------
-- * Pointer operations
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * File handling
--------------------------------------------------------------------------------
-- | Open a file
fopen :: (FileCMD :<: instr, pc ⊑ l) =>
    {- DPrin l -> -} FilePath -> IOMode -> ProgramT instr (Param3 exp pred pc) m (Handle l)
fopen file = singleInj . FOpen file

-- | Close a file
fclose :: (FileCMD :<: instr, pc ⊑ l) => Handle l -> ProgramT instr (Param3 exp pred pc) m ()
fclose = singleInj . FClose

-- | Check for end of file
feof :: (FreeExp exp, FreePred exp Bool, FileCMD :<: instr, Monad m, l ⊑ pc) =>
    Handle l -> ProgramT instr (Param3 exp pred pc) m (exp Bool)
feof = fmap valToExp . singleInj . FEof

class PrintfType l r
  where
    type PrintfExp r :: * -> *
    fprf :: Handle l -> String -> [PrintfArg (PrintfExp r)] -> r

instance (FileCMD :<: instr, a ~ (), pc ⊑ l) =>
    PrintfType l (ProgramT instr (Param3 exp pred pc) m a)
  where
    type PrintfExp (ProgramT instr (Param3 exp pred pc) m a) = exp
    fprf h form as = singleInj $ FPrintf h form (reverse as)

instance (Formattable a, PrintfType l r, exp ~ PrintfExp r) =>
    PrintfType l (exp a -> r)
  where
    type PrintfExp  (exp a -> r) = exp
    fprf h form as = \a -> fprf h form (PrintfArg a : as)

-- | Print to a handle. Accepts a variable number of arguments.
fprintf :: PrintfType l r => Handle l -> String -> r
fprintf h format = fprf h format []

-- | Put a single value to a handle
fput :: forall instr exp pred a m pc l
    .  (Formattable a, FreePred exp a, FileCMD :<: instr, pc ⊑ l)
    => Handle l
    -> String  -- ^ Prefix
    -> exp a   -- ^ Expression to print
    -> String  -- ^ Suffix
    -> ProgramT instr (Param3 exp pred pc) m ()
fput hdl prefix a suffix =
    fprintf hdl (prefix ++ formatSpecPrint (Proxy :: Proxy a) ++ suffix) a

-- | Get a single value from a handle
fget
    :: ( Formattable a
       , pred a
       , FreeExp exp
       , FreePred exp a
       , FileCMD :<: instr
       , Monad m
       , l ⊑ pc
       )
    => Handle l -> ProgramT instr (Param3 exp pred pc) m (exp a)
fget = fmap valToExp . singleInj . FGet

-- | Print to @stdout@. Accepts a variable number of arguments.
printf :: PrintfType KBot r => String -> r
printf = fprintf stdout
{-
-}
