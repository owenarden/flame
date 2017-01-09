{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.IFC
       ( FLA(..), IFC, BFLA(..), BIFC
       , Labeled(..), Lbl, CtlT, ClrT
       , runIFC, runClr
       , (:≽), (:=>=), (:⊑), (:<:)  -- Delegation types
       , Def(..), (≽), (=>=), (⊑), (<:)     -- Delegation constructors
       )
  where

import Flame.TCB.IFC
import Flame.TCB.Assume
