{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.EDSL.IFC where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Flame.Principals
-- import Flame.TCB.Assume
import Data.Int
import Data.Functor.Identity
import Text.PrettyPrint.Mainland

{- EDSL imports -}
import Control.Monad.Operational.Higher
import qualified Control.Monad.State as CMS
import Control.Monad.State.Class

import Language.C.Quote.C
import qualified Language.C.Syntax as C

import Language.C.Monad hiding (inModule)
import qualified Control.Monad.Reader as R
import Language.Embedded.Expression
--import Language.Embedded.Imperative hiding (cedecl, RefCMD, Ref)
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Language.Embedded.Traversal
import Language.Embedded.Imperative.CMD (RefCMD (GetRef), mkParam, mapFunArg, mapFunArgM)

import Flame.Principals

data Label (exp :: * -> *) (l::KPrin) a where
  Label   :: exp a -> Label exp l a
  Unlabel :: (l ⊑ l') => Label exp l a -> (exp a -> Label exp l' b) -> Label exp l' b

type family BindType (exp :: * -> *) a :: * where
  BindType exp a = exp a
  BindType exp a = a

data LABType (exp :: * -> *) (l::KPrin) a where
  LUnit :: LABType exp l () 
  LExp  :: Label exp l a -> LABType exp l a 
  LExt  :: BindType exp a -> LABType exp l a

runLabel :: Label exp l a -> exp a
runLabel (Label v) = v
runLabel (Unlabel lv f) = runLabel (f $ runLabel lv)

newtype LABProgram exp instr pred pc l a = LAB { program :: Program instr (Param2 exp pred) (LABType exp l a) } 

seq :: (pc ⊑ pc', pc ⊑ pc'') => LABProgram exp instr pred pc l ()
    -> LABProgram exp instr pred pc' l' a
    -> LABProgram exp instr pred pc'' l' a
seq lfst lsnd = LAB $ do
  program lfst
  program lsnd

apply :: (pc ⊑ pc', pc ⊑ pc'') => LABProgram exp instr pred pc l a
      -> (LABType exp l a -> LABProgram exp instr pred pc' l' b)
      -> LABProgram exp instr pred pc'' l' b
apply (LAB prog) f = LAB $ do
                             lv <- prog
                             case f lv of
                               LAB p -> p


bind ::  (l ⊑ l', l ⊑ pc') => LABProgram exp instr pred pc l a
     -> (BindType exp a -> LABProgram exp instr pred pc' l' b)
     -> LABProgram exp instr pred pc l' b
bind (LAB prog) f = LAB $ do
                            x <- prog
                            case x of 
                              LUnit  -> error "Result of bound expression is LUnit"
                              LExt v -> do
                                case f v of
                                  LAB p -> p
                              LExp v -> do
                                case f (runLabel v) of
                                  LAB p -> p

lift :: Label exp l a -> LABProgram exp instr pred pc l a
lift = LAB . return . LExp

class HasBackend exp1 exp2 instr pred where
  translateExp :: exp1 a -> Program instr (Param2 exp2 pred) (exp2 a)

reexpressLAB :: forall instr1 instr2 exp1 exp2 pred pc l a b .
              (Reexpressible instr1 instr2 ()
              , HasBackend exp1 exp2 instr2 pred
              , CType a
              )
             => (forall b . exp1 b -> Program instr2 (Param2 exp2 pred) (exp2 b))
             -> LABProgram exp1 instr1 pred pc l a -> LABProgram exp2 instr2 pred pc l a
reexpressLAB f p = LAB $ do
                      x <- reexpress @instr1 @instr2 @_ @exp1 @exp2 f $ program p
                      case x of 
                        LUnit  -> return LUnit
                        LExp v -> do
                          y <- translateExp $ runLabel v
                          return $ LExp $ Label y

compileLAB :: forall instr exp pred pc l a.
              ( HasBackend exp CExp instr pred 
              , Reexpressible instr instr ()
              , Interp instr CGen (Param2 CExp pred)
              , CType a, FreeExp exp, RefCMD :<: instr
              )
           => String -> LABProgram exp instr pred pc l a -> [(String,Doc)]
compileLAB s p = prettyCGen . wrapFunc s $ (interpret . program) (reexpressLAB @instr @instr @exp @CExp translateExp p)

wrapFunc s prog = do
    (_,uvs,params,items) <- inNewFunction $ prog >> addStm [cstm| return 0; |]
    setUsedVars s uvs
    addGlobal [cedecl| int $id:s($params:params){ $items:items }|]

--relabel :: (l ⊑ l') => n exp l a -> n exp l' a
--relabel a = unlabel a label 
--
--protect :: (pc ⊑ l) => exp a -> LABProgram exp instr pred pc l a
--protect = lift . label

--use :: forall exp instr pred l l' pc pc' pc'' a b.
--       (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'')
--    => LABProgram exp instr pred pc l a -> (exp a -> LABProgram exp instr pred pc' l' b) -> LABProgram exp instr pred pc'' l' b
--use x f = apply x $ \x' -> (bind x' f :: LABProgram exp instr pred pc' l' b)
-- 
--reprotect :: forall exp instr pred l l' pc pc' a.
--             (l ⊑ l', pc ⊑ pc', (pc ⊔ l) ⊑ l')
--          => LABProgram exp instr pred pc l a -> LABProgram exp instr pred pc' l' a 
--reprotect x = use x (protect :: exp a -> LABProgram exp instr pred (pc ⊔ l) l' a)
--
--ifmap :: forall exp instr pred l l' pc pc' a b.
--         (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l')
--      => (exp a -> exp b) -> LABProgram exp instr pred pc l a -> LABProgram exp instr pred pc' l' b
--ifmap f x = use x (\x' -> protect (f x') :: LABProgram exp instr pred (pc ⊔ l) l' b)

{-
newtype LCode n instr exp pc l a = LCode { code :: CGen a }
-- TODO?: rewrite these functions to be in Prog instr CExp instead of LCode
interp_lift :: forall instr exp pc l a.
             ( HasCBackend instr exp
             , FreeExp exp
             , HFunctor instr
             , Interp instr CGen (Param3 CExp CType pc)
             , RefCMD :<: instr
             , pc ⊑ l
             ) => Label exp l a -> LCode Label instr CExp pc l a
interp_lift v = LCode $ interpret (transLabel v :: Prog instr CExp pc a)

interp_apply ::( HasCBackend instr exp
             , LABType exp a
             , FreeExp exp
             , HFunctor instr
             , Interp instr CGen (Param3 CExp CType pc)
             , RefCMD :<: instr
             , pc ⊑ pc', pc ⊑ pc''
             ) => LCode Label instr CExp pc l a -> (Label exp l a -> LCode Label instr CExp pc' l' b) -> LCode Label instr CExp pc'' l' b
interp_apply (LCode v) f = LCode $ do
  (a, bodyc) <- inNewBlock $ do
                  vexp  <- v
                  x <- freshVar (Proxy :: Proxy CType)
                  addStm  [cstm| $id:x = $vexp; |]
                  case (f $ valToExp x) of
                    LCode res -> res
  addStm [cstm|{ $items:bodyc }|]
  return a

interp_bind :: forall instr exp pc pc' l l' a b.
             ( HasCBackend instr exp
             , LABType exp a
             , FreeExp exp
             , HFunctor instr
             , Interp instr CGen (Param3 CExp CType pc)
             , RefCMD :<: instr
             , l ⊑ l', l ⊑ pc
             ) => Label exp l a -> (exp a -> LCode Label instr CExp pc l' b) -> LCode Label instr CExp pc' l' b
interp_bind v f = LCode $ do
  (a, bodyc) <- inNewBlock $ do
                  vexp  <- interpret (transLabel v :: Prog instr CExp pc a)
                  x <- freshVar (Proxy :: Proxy CType)
                  addStm  [cstm| $id:x = $vexp; |]
                  case (f $ valToExp x) of
                    LCode res -> res
  addStm [cstm|{ $items:bodyc }|]
  return a

interpLAB :: forall instr exp pc pc' l a.
            ( HasCBackend instr exp
            , FreeExp exp
            , RefCMD :<: instr
            , FreeExp exp
            , HFunctor instr
            , Interp instr CGen (Param3 CExp CType pc)
            , RefCMD :<: instr
            )
         => LAB Label exp pc l a -> LCode Label instr CExp pc l a
interpLAB (Lift lv)    = interp_lift lv
interpLAB (Apply lv f) = LCode $ do
  (a, bodyc) <- inNewBlock $ do
                  vexp  <- code $ interpLAB @instr lv
                  x <- freshVar (Proxy :: Proxy CType)
                  addStm  [cstm| $id:x = $vexp; |]
                  code $ interpLAB @instr (f $ valToExp x)
  addStm [cstm|{ $items:bodyc }|]
  return a
interpLAB (Bind lv f) = LCode $ do
  (a, bodyc) <- inNewBlock $ do
                  vexp  <- interpret (transLabel @instr @_ @_ @_ @pc lv)
                  x <- freshVar (Proxy :: Proxy CType)
                  addStm  [cstm| $id:x = $vexp; |]
                  code $ interpLAB @instr (f $ valToExp x)
  addStm [cstm|{ $items:bodyc }|]
  return a

compileLAB :: forall instr exp pc l a.
              ( HasCBackend instr exp 
              , Reexpressible instr instr ()
              , Interp instr CGen (Param3 CExp CType pc)
              , FreeExp exp, RefCMD :<: instr
              )
           => String -> Prog instr (LAB Label exp pc l) pc a -> [(String,Doc)]
compileLAB s = prettyCGen . wrapFunc s . interpretWithMonad (code . interpLAB @instr)

wrapFunc s prog = do
    (_,uvs,params,items) <- inNewFunction $ prog >> addStm [cstm| return 0; |]
    setUsedVars s uvs
    addGlobal [cedecl| int $id:s($params:params){ $items:items }|]
    -}