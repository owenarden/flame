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
        FLAMonad(..), IFC, Lbl, CtlT, runIFC,
        (:≽), (:>=), (:⊑), (:<:),  -- Delegation types
        (≽), (=>=), (⊑), (<:),     -- Delegation constructors
       )
  where

import Flame.Type.TCB.IFC
