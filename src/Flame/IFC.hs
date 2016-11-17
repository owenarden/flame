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

module Flame.IFC
       ( FLA(..), IFC, Labeled(..), Lbl, CtlT
       , runIFC, runIFCx, runIFCxx
       , (:≽), (:=>=), (:⊑), (:<:)  -- Delegation types
       , Def(..), (≽), (=>=), (⊑), (<:)     -- Delegation constructors
       )
  where

import Flame.TCB.IFC
import Flame.TCB.Assume
