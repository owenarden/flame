--{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
--    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
--{-# LANGUAGE TypeOperators, PostfixOperators #-}
--{-# LANGUAGE OverloadedStrings #-}
--{-# LANGUAGE AllowAmbiguousTypes, UndecidableInstances, IncoherentInstances #-}
--
--{-# LANGUAGE Rank2Types, FlexibleContexts, UndecidableInstances, TypeFamilies #-}
--{-# LANGUAGE ConstraintKinds, KindSignatures, PolyKinds, TypeOperators #-}
--{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
--{-# LANGUAGE FunctionalDependencies #-}

module Flame
--       (Prin(..) , SPrin(..), KPrin(..)
--       , C , I , (:/\:) , (:∧:) , (:\/:) , (:∨:) , (:⊔:) , (:⊓:) , Public , Trusted , PT           
--       , Def(..)
--       , Bound
--       , public, trusted, publicTrusted
--       , IFC, runIFC, protect, relabelIFC, relabelIFCx
--       , Lbl, label, unlabel
--       , assume
--       , DAFType
--       )
  where

import Flame.TCB.Core
  
