{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE DeriveGeneric            #-}
{-# LANGUAGE PostfixOperators         #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.Servant.Auth
  (EnforceFLA, IFCAuth, authorize, IFCApp(..))
where
import Data.Constraint

import GHC.TypeLits                     (KnownNat, natVal)
import Network.HTTP.Types.Status
import Network.HTTP.Types.Method
import Network.HTTP.Types.Header
import Network.Wai                      (Request, requestHeaders, Response)

import Control.Monad.Trans.Resource     (MonadResource (..), ResourceT, runResourceT)
import Data.Maybe                       (fromMaybe)

import Servant 
import Servant.Common.Req
import Servant.Client hiding (Client)
import qualified Servant.Client as C
import Servant.API.ContentTypes
import Servant.Server.Internal
import Servant.Foreign

import Flame.Principals
import Flame.Runtime.Principals
import Flame.Runtime.IO
import Flame.IFC
import Flame.TCB.IFC (unsafeUnlabel)
import Flame.TCB.Assume

import qualified Control.Monad.IO.Class as MIO (liftIO) 

newtype EnforceFLA (pc::KPrin) (l::KPrin) a = EnforceFLA a 
newtype EnforceNM (pc::KPrin) (l::KPrin) a = EnforceNM a

data IFCAuth api where
   IFCAuthorized :: IFCApp api =>
                 DPrin client
              -> (AppServer api :≽: (client ∧ (∇) client)
                 , Client api :===: client)
              -> IFCAuth api

authorize :: (IFCApp api, AppServer api ≽ (client ∧ (∇) client), Client api === client) =>
             DPrin client
          -> IFCAuth api
authorize client = IFCAuthorized client (ActsFor, Equiv)

class IFCApp api where

  type AppServer api :: KPrin
  type Client    api :: KPrin

  -- TODO: how to ensure api is sane for choice of AppServer and Client?

  appServerPrin     :: Proxy api -> Prin
  currentClientPrin :: Proxy api -> Prin
  appServerTy       :: Proxy api -> SPrin (AppServer api)
  currentClientTy   :: Proxy api -> SPrin (Client api)

  appServer :: Proxy api -> DPrin (AppServer api)
  appServer api =  (appServerPrin api) <=> (appServerTy api)
  currentClient :: Proxy api -> DPrin (Client api)
  currentClient api =  (currentClientPrin api) <=> (currentClientTy api)

  mkHandler :: forall pc l a. ( AppServer api ≽ (C (Client api) ∧ I (Client api) ∧ (∇) (Client api))
                              , (I (AppServer api)) ≽ I pc
                              , (I (AppServer api)) ≽ I l
                              , (I (Client api) ∧ C (AppServer api)) ≽ pc
                              , (C (Client api) ∧ I (AppServer api)) ≽ l
                              ) =>
            Proxy api
            -> FLAC IO (I (AppServer api)) (I (AppServer api)) (IFCAuth api)
            -> (forall client. DPrin client -> (Prin, Prin))
            -> DPrin pc
            -> DPrin l
            -> (forall client pc' l'.
                ((AppServer api) ≽ (client ∧ (∇) client), (Client api) === client) =>
                     DPrin client
                  -> DPrin pc' 
                  -> DPrin l'
                  -> Maybe ( pc :===: pc'
                           , l :===: l'
                           , FLAC IO pc' l' a
                           )
               )
            -> FLAC Handler pc l a
  mkHandler api auth_ toPCL pc l f = 
    liftIO $ use (reprotect auth_ :: FLAC IO pc l (IFCAuth api)) $ \auth ->
     case auth of
      IFCAuthorized (client :: DPrin client) (ActsFor, Equiv) ->
       let (pc'_, l'_) = toPCL client in
         withPrin pc'_ $ \(pc' :: DPrin pc') -> 
          withPrin l'_ $ \(l' :: DPrin l') -> 
           case f client pc' l' of
             Just (Equiv, Equiv, h) -> reprotect h
             _ -> error "could not make handler"
    where
      apiClient = currentClient api
      apiAppServer = appServer api