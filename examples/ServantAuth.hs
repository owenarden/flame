{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Based on Servant.API.Experimental.Auth and
-- https://github.com/krdlab/examples/blob/master/haskell-servant-webapp/src/Main.hs
module ServantAuth where

import Prelude hiding (id)

import GHC.TypeLits (KnownNat, KnownSymbol, natVal, symbolVal)
import Network.HTTP.Types.Status
import Network.HTTP.Types.Method
import Network.HTTP.Types.Header

import qualified Control.Monad.IO.Class as XXX (liftIO) 
import Data.Aeson (FromJSON(..), ToJSON(..))
import qualified Data.Map as M
import Data.Text (Text)
import Data.Time (LocalTime(..), TimeZone(..), ZonedTime(..), hoursToTimeZone, midday, fromGregorian, utcToZonedTime, getCurrentTimeZone)
import GHC.Generics (Generic)
import Network.Wai (Application, Response)
import Network.Wai.Handler.Warp (run)
import System.IO as SIO
import Servant ((:>), (:<|>)(..), ReqBody, Capture, Get, Post, Delete, Proxy(..), Server, serve, ServantErr, HasServer(..), reflectMethod, ReflectMethod(..))
import           Servant.API.ContentTypes
import Servant.Docs (docs, ToCapture(..), DocCapture(..), ToSample(..), markdown, singleSample, HasDocs(..))
import Servant.Docs.Internal (ToAuthInfo(..), authInfo, DocAuthentication(..))
import Servant.Server.Internal
import Control.Lens ((|>), over)
import System.Environment (getArgs)

import Data.Maybe  (fromJust, fromMaybe)
import Data.Aeson                       (ToJSON)
import Data.ByteString                  (ByteString)
import Data.Map                         (Map, fromList)
import Data.Monoid                      ((<>))
import qualified Data.Map            as Map
import Data.Proxy                       (Proxy (Proxy))
import Data.Text                        (Text, pack)
import GHC.Generics                     (Generic)
import Network.Wai                      (Request, requestHeaders)
import Servant.API                      ((:<|>) ((:<|>)), (:>), BasicAuth,
                                          Get, JSON, Verb(..))
import Servant.API.BasicAuth            (BasicAuthData (BasicAuthData))
import Servant.API.Experimental.Auth    (AuthProtect)
import Servant                          (throwError)
import Servant.Server                   (BasicAuthCheck (BasicAuthCheck),
                                         BasicAuthResult( Authorized
                                                        , Unauthorized
                                                        ),
                                         Context ((:.), EmptyContext),
                                         err401, err403, errBody, Server,
                                         serveWithContext, Handler,
                                         ServerT, (:~>)(..), Application, serve, enter)
import Servant.Server.Experimental.Auth (AuthHandler, AuthServerData,
                                         mkAuthHandler)
import Servant.Server.Experimental.Auth()
import Control.Monad.Trans.Resource     (MonadResource (..), ResourceT, runResourceT)


import Flame.Runtime.Servant.Auth

import Flame.Runtime.Principals
import Flame.IFC
import Flame.Principals
import Flame.Runtime.Time as T
import Control.Concurrent.STM hiding (atomically)
import Flame.Runtime.STM as F
import qualified Flame.Runtime.Prelude as F hiding (id)
import Flame.Runtime.Sealed
import Flame.Runtime.IO
import Data.String
import System.IO.Unsafe
import Control.Monad.Trans.Either (EitherT)

import Flame.TCB.Assume
import Flame.TCB.IFC (Lbl(..))

--instance ToJSON Prin
--deriving instance Generic Prin

-- These instances require TCB access
--instance ToJSON a => ToJSON (FLAC IO (I Client) Client a) where
--  toJSON la = toJSON $ unsafeUnlabel $ unsafePerformIO (runFLAC la)

--deriving instance Generic (Lbl Client a)

{- Auth specific -}
type Alice = KName "Alice"
alice = Name "Alice"

type Bob = KName "Bob"
bob = Name "Bob"

type Carol = KName "Carol"
carol = Name "Carol"

-- | A database mapping keys to users.
prin_database :: FLAC IO (I AppServer) AppServer (Map ByteString Prin)
prin_database = protect $ fromList [ ("key1", alice)
                                   , ("key2", bob)
                                   , ("key3", carol)
                                   ]
authit :: Prin -> (forall client. DPrin client -> Maybe (s :≽: (client ∧ (∇) client), c :===: client))
authit = undefined
                                 
-- | A method that, when given a password, will return a Prin.
-- This is our bespoke (and bad) authentication logic.
lookupPrin :: ByteString -> Handler (FLAC IO (I AppServer) (I AppServer) Prin)
lookupPrin key = return $
    assume2 (SConf SBot ≽ SConf (st $ appServer memoAPI)) $
      use prin_database $ \database ->
      case Map.lookup key database of
        Nothing ->  protect $ undefined --throwError (err403 { errBody = "Invalid Cookie" })
        Just usr -> protect $ usr

-- | The auth handler wraps a function from Request -> Handler Prin
-- we look for a Cookie and pass the value of the cookie to `lookupPrin`.
authHandler :: AuthHandler Request (FLAC IO (I AppServer) (I AppServer) Prin)
authHandler =
  let handler req = case lookup "servant-auth-cookie" (requestHeaders req) of
        Nothing -> throwError (err401 { errBody = "Missing auth header" })
        Just authCookieKey -> lookupPrin authCookieKey
  in mkAuthHandler handler

-- | We need to specify the data returned after authentication
type instance AuthServerData (AuthProtect "cookie-auth") = FLAC IO (I AppServer) (I AppServer) Prin

{- memo specific -}
data Memo = Memo
    { id :: Int
    , text :: Text
    , createdAt :: UTCTime
    }
    deriving (Show, Generic)

instance ToJSON Memo

data ReqMemo = ReqMemo { memo :: Text } deriving (Show, Generic)

instance FromJSON ReqMemo
instance ToJSON ReqMemo

type MemoAPI =
         "memos" :> AuthProtect "cookie-auth"
          :> EnforceFLA (I Client) (Client) (Get '[JSON] [Memo]) 
    :<|> "memos" :> AuthProtect "cookie-auth"
          :> ReqBody '[JSON] ReqMemo
          :> EnforceFLA (I Client) (Client) (Post '[JSON] Memo) 
    :<|> "memos" :> AuthProtect "cookie-auth"
         :> Capture "id" Int
         :>  EnforceFLA (I Client) (Client) (Delete '[JSON] ())

memoAPI :: Proxy MemoAPI
memoAPI = Proxy

type MemoStore = Lbl (I AppServer) MemoDB
type MemoDB = IFCTVar (I AppServer) (M.Map Prin (SealedType IFCTVar (Int, M.Map Int Memo)))

-- | The context that will be made available to request handlers. We supply the
-- "cookie-auth"-tagged request handler defined above, so that the 'HasServer' instance
-- of 'AuthProtect' can extract the handler and run it on the request.
genAuthServerContext :: Context (AuthHandler Request (FLAC IO (I AppServer) (I AppServer) Prin) ': '[])
genAuthServerContext = authHandler :. EmptyContext

main :: IO ()
main = do
    args <- getArgs
    case args of
        --["d"] -> putStrLn doc
        ["s"] -> runApp
        _     -> putStrLn "unknown option"

runApp :: IO ()
runApp = do 
  init <- runFLAC $ use initialMemoStore $ \store -> newIFCTVarIO store
  run 8080 $ app init

  where
    newMemoDB :: DPrin p
              -> FLAC IO (I AppServer) (I AppServer)
                  (IFCTVar p (Int, M.Map Int Memo))
    newMemoDB p = newIFCTVarIO (0, M.empty)

    initialMemoStore :: FLAC IO (I AppServer) (I AppServer)
                         (M.Map Prin (SealedType IFCTVar (Int, M.Map Int Memo)))
    initialMemoStore =
      withPrin alice $ \alice' -> withPrin bob $ \bob' -> withPrin carol $ \carol' -> 
        use (newMemoDB alice') $ \aliceDB ->
        use (newMemoDB bob')   $ \bobDB ->
        use (newMemoDB carol') $ \carolDB ->
        protect $ fromList [ (alice, sealType alice' aliceDB)
                           , (bob,   sealType bob'   bobDB)
                           , (carol, sealType carol' carolDB)
                           ]

app :: MemoStore -> Application
app s = serveWithContext memoAPI genAuthServerContext $ server s

--doc :: String
--doc = markdown $ docs memoAPI

{- common defs -}
type Client = KName "Client"
-- currentClient :: SPrin Client
-- currentClient = 

type AppServer = KTop
--appServer :: SPrin KTop
--appServer = STop

instance IFCApp AppServer Client MemoAPI where
  appServerPrin = const $ Top
  appServerTy   = const $ STop

  currentClientPrin = const $ Name "Client"
  currentClientTy   = const $ SName (Proxy :: Proxy "Client")

server :: MemoStore -> Server MemoAPI
server s = getMemosH :<|> postMemoH :<|> deleteMemoH
  where
    auth :: forall client. DPrin client -> Maybe (AppServer :≽: (client ∧ (∇) client), Client :===: client)
    auth = undefined

    apiClient = currentClient memoAPI
    apiAppServer = appServer memoAPI
    mkSig client = (dyn (client^←), dyn client)
    deleteMemoH :: FLAC IO (I AppServer) (I AppServer) Prin
                 -> Int
                 -> FLAC Handler (I Client) Client ()
    deleteMemoH p i = mkHandler memoAPI p undefined mkSig (apiClient^←) apiClient $
       \client pc' l' -> do
          Equiv <- pc' `eq` (client^←)
          Equiv <- l' `eq` client
          (ActsFor, Equiv) <- auth client
          return (Equiv, Equiv, reprotect $ ebind s $ \db -> deleteMemo client db i)

    getMemosH :: FLAC IO (I AppServer) (I AppServer) Prin
              -> FLAC Handler (I Client) Client [Memo]
    getMemosH p = mkHandler memoAPI p undefined undefined (apiClient^←) apiClient undefined
    --getMemosH p = mkHandler p getMemos

    postMemoH :: FLAC IO (I AppServer) (I AppServer) Prin
              -> ReqMemo
              -> FLAC Handler (I Client) Client Memo
    postMemoH p r = mkHandler memoAPI p undefined undefined (apiClient^←) apiClient undefined
    --postMemoH p r = mkHandler p $ postMemo r

deleteMemo :: DPrin client
           -> MemoDB
           -> Int
           -> FLAC IO (I client) client ()
deleteMemo client db i = undefined
{- 
withMemoDB :: forall client b .
             DPrin client
             -> MemoDB
             -> (forall client'. (client === client') =>
                                 DPrin client'
                              -> IFCTVar client' (Int, (M.Map Int Memo))
                              -> FLAC STM (I client) client b)
             -> FLAC STM (I client) client b
withMemoDB client db f =
  use (readIFCTVar db) $ \db' -> 
  fromJust $ do -- TODO: handle Nothing case!
   entry <- M.lookup (dyn client) db'
   unsealTypeWith @client @IFCTVar @(Int, Map Int Memo) @(FLAC STM (I client) client b)
           client entry f

getMemos :: (Client === client, client === l) =>
            DPrin client
         -> MemoDB
         -> FLAC IO (I client) client [Memo]
getMemos client db = atomically $
    withMemoDB client db $ \(client':: DPrin l) db' ->
    use (readIFCTVar db') $ \(_, m) ->
    protect $ M.elems m

postMemo :: (Client === client, client === l) =>
            ReqMemo
         -> DPrin client
         -> MemoDB
         -> FLAC IO (I client) client Memo
postMemo req client db =
   use getCurrentTime $ \time -> atomically $
   withMemoDB client db $ \(client':: DPrin l) db' ->
   use (readIFCTVar db') $ \(c, sm) ->
     let m = Memo (c + 1) (memo req) time
         entry = (id m, M.insert (id m) m sm)
     in
       apply (writeIFCTVar db' entry) $ \m' ->
       use (readIFCTVar db') $ \(c', sm') ->
       protect m

deleteMemo :: (Client === client, client === l) =>
              Int
           -> DPrin client
           -> MemoDB
           -> FLAC IO (I client) client ()
deleteMemo i client db = atomically $
  withMemoDB client db $ \(client':: DPrin l) db' ->
  modifyIFCTVar db' $ \(c, sm) ->
  (c, M.delete i sm)
-}
-- NOTE: ↓ for documentation
instance ToCapture (Capture "id" Int) where
    toCapture _ = DocCapture "id" "memo id"

instance ToSample Memo where
    toSamples _ = singleSample sampleMemo

instance ToSample [Memo] where
    toSamples _ = singleSample [sampleMemo]

instance ToSample ReqMemo where
    toSamples _ = singleSample $ ReqMemo "Try haskell-servant."

instance ToSample (FLAC IO (I Client) Client Memo) where
    toSamples _ = singleSample $ protect sampleMemo

instance ToSample (FLAC IO (I Client) Client [Memo]) where
    toSamples _ = singleSample $ protect [sampleMemo]

instance ToSample (FLAC IO (I Client) Client ()) where
    toSamples _ = singleSample $ protect ()

sampleMemo :: Memo
sampleMemo = Memo
    { id = 5
    , text = "Try haskell-servant."
    , createdAt = UTCTime (fromGregorian 2014 12 31) (secondsToDiffTime 0)
    }

instance (ToAuthInfo (AuthProtect "cookie-auth"), HasDocs api) => HasDocs (AuthProtect "cookie-auth" :> api) where
  docsFor Proxy (endpoint, action) =
    docsFor (Proxy :: Proxy api) (endpoint, action')
      where
        authProxy = Proxy :: Proxy (AuthProtect "cookie-auth")
        action' = over authInfo (|> toAuthInfo authProxy) action

instance ToAuthInfo (AuthProtect "cookie-auth") where
  toAuthInfo p = DocAuthentication "servant-auth-cookie" "A key in the principal database"