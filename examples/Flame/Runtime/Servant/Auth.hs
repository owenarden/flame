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
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE UndecidableSuperClasses  #-}
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
  (EnforceFLA, IFCAuth(..), authorize, IFCApp(..))
where
import Data.Constraint

import GHC.TypeLits                     (KnownNat, natVal)
import Network.HTTP.Types.Status
import Network.HTTP.Types.Method
import Network.HTTP.Types.Header
import Network.Wai                      (Request, requestHeaders, Response)

import Control.Monad.Trans.Resource     (MonadResource (..), ResourceT, runResourceT)
import Data.Maybe                       (fromMaybe)

import Servant.API.ContentTypes
import Servant.Server.Internal

import Flame.Principals
import Flame.Runtime.Principals
import Flame.Runtime.IO
import Flame.IFC
import Flame.TCB.IFC (unsafeUnlabel)
import Flame.TCB.Assume

import qualified Control.Monad.IO.Class as MIO (liftIO) 

import Servant 

newtype EnforceFLA (pc::KPrin) (l::KPrin) a = EnforceFLA a 
newtype EnforceNM (pc::KPrin) (l::KPrin) a = EnforceNM a


{-- XXX: why doesn't this more general instance work? -}
instance (AllCTRender ctypes a, ReflectMethod method, KnownNat status,
 HasServer (Verb method status ctypes a) context) =>
  HasServer (EnforceFLA pc l (Verb method status ctypes a)) context where
    type ServerT (EnforceFLA pc l (Verb method status ctypes a)) e =
      FLAC e pc l a 
       
    route Proxy _ action = flacMethodRouter method_ (Proxy :: Proxy ctypes) status action
      where method_ = reflectMethod (Proxy :: Proxy method)
            status = toEnum . fromInteger $ natVal (Proxy :: Proxy status)

instance (AllCTRender ctypes a, HasServer (Get ctypes a) context) =>
  HasServer (EnforceFLA pc l (Get ctypes a)) context where
    type ServerT (EnforceFLA pc l (Get ctypes a)) e = FLAC e pc l a 
       
    route Proxy _ action = flacMethodRouter method (Proxy :: Proxy ctypes) status action
      where method = reflectMethod (Proxy :: Proxy GET)
            status = toEnum . fromInteger $ 200

instance (AllCTRender ctypes a, HasServer (Post ctypes a) context) =>
  HasServer (EnforceFLA pc l (Post ctypes a)) context where
    type ServerT (EnforceFLA pc l (Post ctypes a)) e = FLAC e pc l a 
       
    route Proxy _ action = flacMethodRouter method (Proxy :: Proxy ctypes) status action
      where method = reflectMethod (Proxy :: Proxy POST)
            status = toEnum . fromInteger $ 200

-- | Adapted to Flame from methodRouter in Servant.Server.Internal  (v0.10)
instance (AllCTRender ctypes a, HasServer (Delete ctypes a) context) =>
  HasServer (EnforceFLA pc l (Delete ctypes a)) context where
    type ServerT (EnforceFLA pc l (Delete ctypes a)) e = FLAC e pc l a 
       
    route Proxy _ action = flacMethodRouter method (Proxy :: Proxy ctypes) status action
      where method = reflectMethod (Proxy :: Proxy DELETE)
            status = toEnum . fromInteger $ 200
flacMethodRouter :: (AllCTRender ctypes a)
             => Method -> Proxy ctypes -> Status
             -> Delayed env (FLACT Handler Lbl pc l a)
             -> Router env
flacMethodRouter method proxy status action = leafRouter route'
  where
    route' env request respond =
          let accH = fromMaybe ct_wildcard $ lookup hAccept $ requestHeaders request
          in flacRunAction (action `addMethodCheck` methodCheck method request
                               `addAcceptCheck` acceptCheck proxy accH
                       ) env request respond $ \ output -> do
               let handleA = handleAcceptH proxy (AcceptHeader accH) output
               processMethodRouter handleA status method Nothing request

-- | Adapted to Flame from runAction in Servant.Server.Internal.RoutingApplication (v0.10)
flacRunAction :: forall env pc l a r. Delayed env (FLACT Handler Lbl pc l a)
          -> env
          -> Request
          -> (RouteResult Response -> IO r)
          -> (a -> RouteResult Response)
          -> IO r
flacRunAction action env req respond k = runResourceT $ do
    runDelayed action env req >>= \res ->
      go res >>= \res' ->
        MIO.liftIO (respond res')
 where
   go :: RouteResult (FLAC Handler pc l a) -> (ResourceT IO) (RouteResult Response)
   go (Fail e)      = return $ Fail e
   go (FailFatal e) = return $ FailFatal e
   go (Route a)     = MIO.liftIO $ do
     e <- runHandler $ runFLAC a
     case e of
       Left err -> return . Route $ responseServantErr err
       Right x  -> return $! k (unsafeUnlabel x)

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