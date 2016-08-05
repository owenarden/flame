{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

module Flame.Type.IFC
       (
          FLAMonad(..), IFC, Lbl (MkLbl), CtlT, runIFC, use, label, relabel
        , (:≽), (:=>=), (:⊑), (:<:)  -- Delegation types
        , Def(..), (≽), (=>=), (⊑), (<:)     -- Delegation constructors
        , unlabel
       )
  where

import Flame.Type.TCB.IFC
