{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

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

-- | C code generation for imperative commands

module Flame.EDSL.Backend.C where



#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad.State
import Data.Proxy

import Language.C.Quote.GCC
import qualified Language.C.Syntax as C

import Control.Monad.Operational.Higher
import Language.C.Monad
import Language.Embedded.Expression
import Language.Embedded.Imperative.Frontend.General
import Language.Embedded.Backend.C hiding (proxyPred)

import Flame.EDSL.CMD

-- | Get the type predicate from an instruction type
proxyPred :: cmd (Param4 p e pred pc) a -> Proxy pred
proxyPred _ = Proxy


-- | Compile `RefCMD`
compRefCMD :: (CompExp exp, CompTypeClass ct) =>
    RefCMD (Param4 prog exp ct pc) a -> CGen a
compRefCMD cmd@(NewRef base) = do
    t <- compType (proxyPred cmd) (proxyArg cmd)
    r <- RefComp <$> gensym base
    addLocal $ case t of
      C.Type _ C.Ptr{} _ -> [cdecl| $ty:t $id:r = NULL; |]
      _                  -> [cdecl| $ty:t $id:r; |]
    return r
compRefCMD cmd@(InitRef base exp) = do
    t <- compType (proxyPred cmd) exp
    r <- RefComp <$> gensym base
    e <- compExp exp
    addLocal [cdecl| $ty:t $id:r; |]
    addStm   [cstm| $id:r = $e; |]
    return r
compRefCMD cmd@(GetRef ref) = do
    v <- freshVar (proxyPred cmd)
    touchVar ref
    addStm [cstm| $id:v = $id:ref; |]
    return v
compRefCMD (SetRef ref exp) = do
    v <- compExp exp
    touchVar ref
    addStm [cstm| $id:ref = $v; |]
compRefCMD (UnsafeFreezeRef (RefComp v)) = return $ ValComp v


-- | Compile `ControlCMD`
compControlCMD :: (CompExp exp, CompTypeClass ct) =>
    ControlCMD (Param4 CGen exp ct pc) a -> CGen a
compControlCMD (If c t f) = do
    cc <- compExp c
    case cc of
      C.Var (C.Id "true"  _) _  -> t
      C.Var (C.Id "false"  _) _ -> f
      _ -> do
        ct <- inNewBlock_ t
        cf <- inNewBlock_ f
        case (ct, cf) of
          ([],[]) -> return ()
          (_ ,[]) -> addStm [cstm| if (   $cc) {$items:ct} |]
          ([],_ ) -> addStm [cstm| if ( ! $cc) {$items:cf} |]
          (_ ,_ ) -> addStm [cstm| if (   $cc) {$items:ct} else {$items:cf} |]
compControlCMD (While cont body) = do
    s <- get
    noop <- do
        conte <- cont
        contc <- compExp conte
        case contc of
          C.Var (C.Id "false"  _) _ -> return True
          _ -> return False
    put s
    bodyc <- inNewBlock_ $ do
        conte <- cont
        contc <- compExp conte
        case contc of
          C.Var (C.Id "true"  _) _ -> return ()
          _ -> case viewNotExp contc of
              Just a -> addStm [cstm| if ($a) {break;} |]
              _      -> addStm [cstm| if (! $contc) {break;} |]
        body
    when (not noop) $ addStm [cstm| while (1) {$items:bodyc} |]
compControlCMD cmd@(For (lo,step,hi) body) = do
    loe <- compExp lo
    hie <- compExp $ borderVal hi
    i   <- freshVar (proxyPred cmd)
    bodyc <- inNewBlock_ (body i)
    let incl = borderIncl hi
    let conte
          | incl && (step>=0) = [cexp| $id:i<=$hie |]
          | incl && (step<0)  = [cexp| $id:i>=$hie |]
          | step >= 0         = [cexp| $id:i< $hie |]
          | step < 0          = [cexp| $id:i> $hie |]
    let stepe
          | step == 1    = [cexp| $id:i++ |]
          | step == (-1) = [cexp| $id:i-- |]
          | step == 0    = [cexp| 0 |]
          | step >  0    = [cexp| $id:i = $id:i + $step |]
          | step <  0    = [cexp| $id:i = $id:i - $(negate step) |]
    addStm [cstm| for ($id:i=$loe; $conte; $stepe) {$items:bodyc} |]
compControlCMD Break = addStm [cstm| break; |]
compControlCMD (Assert cond msg) = do
    addInclude "<assert.h>"
    c <- compExp cond
    addStm [cstm| assert($c && $msg); |]

compIOMode :: IOMode -> String
compIOMode ReadMode      = "r"
compIOMode WriteMode     = "w"
compIOMode AppendMode    = "a"
compIOMode ReadWriteMode = "r+"

-- | Compile `FileCMD`
compFileCMD :: (CompExp exp, CompTypeClass ct, ct Bool) =>
    FileCMD (Param4 prog exp ct pc) a -> CGen a
compFileCMD (FOpen path mode) = do
    addInclude "<stdio.h>"
    addInclude "<stdlib.h>"
    sym <- gensym "f"
    addLocal [cdecl| typename FILE * $id:sym; |]
    addStm   [cstm| $id:sym = fopen($id:path',$string:mode'); |]
    return $ HandleComp sym
  where
    path' = show path
    mode' = compIOMode mode
compFileCMD (FClose h) = do
    addInclude "<stdio.h>"
    touchVar h
    addStm [cstm| fclose($id:h); |]
compFileCMD (FPrintf h form as) = do
    addInclude "<stdio.h>"
    touchVar h
    let h'     = [cexp| $id:h |]
        form'  = show form
        form'' = [cexp| $id:form' |]
    as' <- fmap ([h',form'']++) $ sequence [compExp a | PrintfArg a <- as]
    addStm [cstm| fprintf($args:as'); |]
compFileCMD cmd@(FGet h) = do
    addInclude "<stdio.h>"
    v <- freshVar (proxyPred cmd)
    touchVar h
    let mkProxy = (\_ -> Proxy) :: FileCMD (Param4 prog exp pred pc) (Val a) -> Proxy a
        form    = formatSpecScan (mkProxy cmd)
    addStm [cstm| fscanf($id:h, $string:form, &$id:v); |]
    return v
compFileCMD cmd@(FEof h) = do
    addInclude "<stdbool.h>"
    addInclude "<stdio.h>"
    v <- freshVar (proxyPred cmd)
    touchVar h
    addStm [cstm| $id:v = feof($id:h); |]
    return v

instance (CompExp exp, CompTypeClass ct)          => Interp RefCMD     CGen (Param3 exp ct pc) where interp = compRefCMD
instance (CompExp exp, CompTypeClass ct)          => Interp ControlCMD CGen (Param3 exp ct pc) where interp = compControlCMD
instance (CompExp exp, CompTypeClass ct, ct Bool) => Interp FileCMD    CGen (Param3 exp ct pc) where interp = compFileCMD