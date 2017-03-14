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

module Flame.Runtime.Servant.Auth.Client
  (EnforceFLA, IFCAuth, authorize, IFCApp(..))
where
import Data.Constraint
import Data.Foldable (toList)
import Control.Monad
import Data.String.Conversions (cs)
import Control.Monad.Reader hiding (liftIO)
import Control.Exception

import GHC.TypeLits                     (KnownNat, natVal)
import Network.HTTP.Media
import Network.HTTP.Types.Status
import Network.HTTP.Types.Method
import qualified Network.HTTP.Types         as H
import qualified Network.HTTP.Types.Header  as HTTP
import qualified Network.HTTP.Client as WC

import Network.Wai                      (Request, requestHeaders)

import Control.Monad.Trans.Resource     (MonadResource (..), ResourceT, runResourceT)
import Data.Maybe                       (fromMaybe)

import Servant 
import Servant.Common.Req
import Servant.Client hiding (Client)
import qualified Servant.Client as C
import Servant.API.ContentTypes
import Servant.Common.BaseUrl


import Flame.Principals
import Flame.Runtime.Principals
import Flame.Runtime.IO
import Flame.IFC
import Flame.TCB.IFC (unsafeUnlabel)
import Flame.TCB.Assume
import Flame.Runtime.Servant.Auth

import Data.ByteString.Lazy (ByteString)

import qualified Control.Monad.IO.Class as MIO (liftIO) 

{- OVERLAPPING -}
instance (MimeUnrender ct a, cts' ~ (ct ': cts)
         , ReflectMethod method, HasClient (Verb method status cts' a)
         ) => HasClient (EnforceFLA pc l (Verb method status cts' a)) where
  type Client (EnforceFLA pc l (Verb method status cts' a))
    = FLACT ClientM Lbl pc l a
  clientWithRoute Proxy req =
       use (flacPerformRequestCT (Proxy :: Proxy ct) method req) $ \(_, res) ->
        protect res
      where method = reflectMethod (Proxy :: Proxy method)

{- OVERLAPPABLE -}
instance -- Note [Non-Empty Content Types]
  (MimeUnrender ct a, cts' ~ (ct ': cts)
  ) => HasClient (EnforceFLA pc l (Get cts' a)) where
  type Client (EnforceFLA pc l (Get cts' a)) = FLAC ClientM pc l a
  clientWithRoute Proxy req =
        use (flacPerformRequestCT (Proxy :: Proxy ct) method req) $ \(_, res) ->
         protect res
      where method = reflectMethod (Proxy :: Proxy GET)

{- OVERLAPPABLE -}
instance -- Note [Non-Empty Content Types]
  (MimeUnrender ct a, cts' ~ (ct ': cts)
  ) => HasClient (EnforceFLA pc l (Post cts' a)) where
  type Client (EnforceFLA pc l (Post cts' a)) = FLACT ClientM Lbl pc l a
  clientWithRoute Proxy req =
        use (flacPerformRequestCT (Proxy :: Proxy ct) method req) $ \(_, res) ->
         protect res
      where method = reflectMethod (Proxy :: Proxy POST)

{- OVERLAPPABLE -}
instance -- Note [Non-Empty Content Types]
  (MimeUnrender ct a, cts' ~ (ct ': cts)
  ) => HasClient (EnforceFLA pc l (Delete cts' a)) where
  type Client (EnforceFLA pc l (Delete cts' a)) = FLACT ClientM Lbl pc l a

  clientWithRoute Proxy req =
        use (flacPerformRequestCT (Proxy :: Proxy ct) method req) $ \(_, res) ->
         protect res
      where method = reflectMethod (Proxy :: Proxy DELETE)

flacPerformRequest :: Method -> Req 
               -> FLAC ClientM pc l ( Int, ByteString, MediaType
                          , [HTTP.Header], WC.Response ByteString)
flacPerformRequest reqMethod req = unsafeProtect $ do
  m <- asks manager
  reqHost <- asks baseUrl
  partialRequest <- MIO.liftIO $ reqToRequest req reqHost

  let request = partialRequest { WC.method = reqMethod }

  eResponse <- MIO.liftIO $ catchConnectionError $ WC.httpLbs request m
  case eResponse of
    Left err ->
      throwError . ConnectionError $ SomeException err

    Right response -> do
      let status = WC.responseStatus response
          body = WC.responseBody response
          hdrs = WC.responseHeaders response
          status_code = statusCode status
      ct <- case lookup "Content-Type" $ WC.responseHeaders response of
                 Nothing -> pure $ "application"//"octet-stream"
                 Just t -> case parseAccept t of
                   Nothing -> throwError $ InvalidContentTypeHeader (cs t) body
                   Just t' -> pure t'
      unless (status_code >= 200 && status_code < 300) $
        throwError $ FailureResponse status ct body
      return $ label (status_code, body, ct, hdrs, response)

flacPerformRequestCT :: MimeUnrender ct result => Proxy ct -> Method -> Req 
    -> FLAC ClientM pc l ([HTTP.Header], result)
flacPerformRequestCT ct reqMethod req = 
  let acceptCTS = contentTypes ct in
   use (flacPerformRequest reqMethod (req { reqAccept = toList acceptCTS })) $ \(_status, respBody, respCT, hdrs, _response) ->
     --unless (any (matches respCT) acceptCTS) $ throwError $ UnsupportedContentType respCT respBody
     case mimeUnrender ct respBody of
       Left err -> error "foobar" -- throwError $ DecodeFailure err respCT respBody
       Right val -> protect (hdrs, val)


