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
          FLAMonad(..), IFC, Lbl (MkLbl), CtlT, runIFC, runIFCx, runIFCxx, use
        , (:≽), (:=>=), (:⊑), (:<:)  -- Delegation types
        , Def(..), (≽), (=>=), (⊑), (<:)     -- Delegation constructors
        , relabel, label, unlabelPT, unlabelUnit
       )
  where

import Flame.Type.TCB.IFC
