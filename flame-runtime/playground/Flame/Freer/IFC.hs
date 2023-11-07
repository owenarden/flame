{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
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
{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

import Flame.Principals
import Control.Monad.Freer
import Data.Proxy

data (l::KPrin) ! a  where
  UnsafeMkLbl :: { unsafeRunLbl :: a } -> l!a

data Eval (pc::KPrin) a  where
  UnsafeMkEval :: { unsafeEval :: a } -> Eval pc a

data LabeledSig a where 
    Return :: (pc ⊑ l) => Proxy pc -> Proxy l -> a -> LabeledSig (Eval pc (l!a))
    Bind :: (l ⊑ l', l ⊑ pc) => Proxy pc -> Proxy l -> Proxy l' 
        -> l!a -> (a -> Eval pc (l'!b)) -> LabeledSig (Eval pc (l'!b))

return :: (Member LabeledSig effs,  pc ⊑ l) => Proxy pc -> Proxy l -> a -> Eff effs (Eval pc (l!a))
return pc l a = send (Return pc l a)

bind :: (Member LabeledSig effs, l ⊑ l', l ⊑ pc) => Proxy pc -> Proxy l -> Proxy l' 
           -> l!a -> (a -> Eval pc (l'!b)) -> Eff effs (Eval pc (l'!b))
bind pc l l' la k = send (Bind pc l l' la k)

main :: IO ()
main = undefined