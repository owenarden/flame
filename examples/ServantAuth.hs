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

import Control.Monad.IO.Class (liftIO)
import Data.Aeson (FromJSON(..), ToJSON(..))
import qualified Data.Map as M
import Data.Text (Text)
import Data.Time (LocalTime(..), TimeZone(..), ZonedTime(..), hoursToTimeZone, midday, fromGregorian, utcToZonedTime, getCurrentTime, getCurrentTimeZone)
import GHC.Generics (Generic)
import Network.Wai (Application)
--import Network.Wai.Handler.Warp (run)
import System.IO as SIO
import Servant ((:>), (:<|>)(..), ReqBody, Capture, Get, Post, Delete, Proxy(..), Server, serve)
import Servant.Docs (docs, ToCapture(..), DocCapture(..), ToSample(..), markdown, singleSample, HasDocs(..))
import Servant.Docs.Internal -- (ToAuthInfo(..), authInfo)
import Control.Lens ((|>), over)
import System.Environment (getArgs)

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
                                          Get, JSON)
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

import Flame.Runtime.Principals
import Flame.IFC
import Flame.TCB.IFC (Lbl(..))
import Flame.Principals
import Flame.Runtime.Time as T
import Flame.Runtime.STM
import qualified Flame.Runtime.Prelude as F hiding (id)
import Flame.Runtime.Warp as F (run)
import Flame.Runtime.Sealed
import Data.String

{- common defs -}
type Client = KName "Client"
currentClient :: SPrin Client
currentClient = SName (Proxy :: Proxy "Client")

type AppServer = KTop
appServer :: SPrin KTop
appServer = STop

instance ToJSON Prin
deriving instance Generic Prin

-- These instances require TCB access
instance ToJSON a => ToJSON (Lbl Client a) where
  toJSON la = toJSON (unsafeRunLbl la)

deriving instance Generic (Lbl Client a)

type SealedHandler e a = SealedIFC FLACT e Lbl a

mkFLACHandler :: (Monad e, AppServer ≽ Client) =>
                 Prin
              -> (forall client. (AppServer ≽ Client, Client === client) =>
                   DPrin client -> FLAC e (I client) client a)
              -> FLAC IO (I AppServer) (I AppServer) (SealedHandler e a)
mkFLACHandler p@(Name n) func =  -- XXX: Generalize to check for (p ≽ (I p ∧ (∇) p))
  withPrin p $ \(client :: DPrin client) -> 
    let sclient = (st client) in
      assume2 (currentClient ≽ sclient) $
        assume2 (sclient ≽ currentClient) $
          protect $ sealIFC (client^←) client $ func client

{- Auth specific -}
type Alice = KName "Alice"
alice = Name "Alice"

type Bob = KName "Bob"
bob = Name "Bob"

type Carol = KName "Carol"
carol = Name "Carol"

-- | A user type that we "fetch from the database" after
-- performing authentication
-- newtype Prin = Prin { unPrin :: Text}

-- | A database mapping keys to users.
prin_database :: FLAC IO (I AppServer) AppServer (Map ByteString Prin)
prin_database = protect $ fromList [ ("key1", alice)
                                   , ("key2", bob)
                                   , ("key3", carol)
                                   ]
                                 
-- | A method that, when given a password, will return a Prin.
-- This is our bespoke (and bad) authentication logic.
lookupPrin :: ByteString -> Handler (FLAC IO (I AppServer) (I AppServer) Prin)
lookupPrin key = return $
    assume2 (SConf SBot ≽ SConf appServer) $
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
          :> Get  '[JSON] (Lbl Client [Memo])
    :<|> "memos" :> AuthProtect "cookie-auth"
          :> ReqBody '[JSON] ReqMemo
          :> Post '[JSON] (Lbl Client Memo) 
    :<|> "memos" :> AuthProtect "cookie-auth"
         :> Capture "id" Int
         :>  Delete '[JSON] ()

memoAPI :: Proxy MemoAPI
memoAPI = Proxy

type MemoStore = FLAC IO (I AppServer) (I AppServer) MemoDB
type MemoDB = IFCTVar (I AppServer) (M.Map Prin (SealedType IFCTVar (Int, M.Map Int Memo)))

-- TODO: A SealedMap that enforces the envariant that mapped values are sealed by their keys?

-- | The context that will be made available to request handlers. We supply the
-- "cookie-auth"-tagged request handler defined above, so that the 'HasServer' instance
-- of 'AuthProtect' can extract the handler and run it on the request.
genAuthServerContext :: Context (AuthHandler Request (FLAC IO (I AppServer) (I AppServer) Prin) ': '[])
genAuthServerContext = authHandler :. EmptyContext

main :: IO ()
main = do
    args <- getArgs
    case args of
        ["d"] -> putStrLn doc
        ["s"] -> runApp
        _     -> putStrLn "unknown option"

runApp :: IO ()
runApp = run 8080 $ app (newIFCTVarIO initialMemoDB)
  where
    newMemoDB :: DPrin p
              -> FLAC IO (I AppServer) (I AppServer)
                  (IFCTVar p (Int, M.Map Int Memo))
    newMemoDB p = newIFCTVarIO (0, M.empty)

    initialMemoDB :: FLAC IO (I AppServer) (I AppServer)
                      (M.Map Prin (SealedType IFCTVar (Int, M.Map Int Memo)))
    initialMemoDB =
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

doc :: String
doc = markdown $ docs memoAPI

server :: MemoStore -> Server MemoAPI
server s = getMemosH :<|> postMemoH :<|> deleteMemoH
  where
    getHandler :: FLAC IO (I AppServer) (I AppServer) (SealedHandler e a)
               -> IO (SealedHandler e a)
    getHandler mh = do
      h <- runFLAC mh
      return $ unlabelPT $ relabel h
    deleteMemoH p i = liftIO $ getHandler $
                        use s $ \db -> 
                        use p $ \client -> mkFLACHandler @IO @() client (deleteMemo db i)
    getMemosH p     = liftIO $ getHandler $
                        use s $ \db -> 
                        use p $ \client -> mkFLACHandler @IO @[Memo] client (getMemos db)
    postMemoH p t   = liftIO $ getHandler $
                        use s $ \db -> 
                        use p $ \client -> mkFLACHandler @IO @Memo client (postMemo db t)

getMemos :: forall client. (Client === client) =>
            MemoDB
         -> DPrin client
         -> FLAC IO (I client) client [Memo]
getMemos store client = undefined
--getMemos store client =
--    use (readIFCTVarIO store) $ \(_, m) ->
--    protect $ M.elems m

postMemo :: forall client. (Client === client) =>
            MemoDB
         -> ReqMemo
         -> DPrin client
         -> FLAC IO (I client) client Memo
postMemo store req client = undefined
--postMemo store req client =
--    use T.getCurrentTime $ \t ->
--    atomically $ 
--     use (readIFCTVar store) $ \store' ->
--     case M.lookup (dyn client) store' of
--       Just memodb -> 
--       let  m = Memo (c + 1) (memo req) t
--            sm' = M.insert (id m) m sm 
--       in apply (writeIFCTVar store $ M.insert (Ex client) sm' store') $ \_ -> 
--          protect m

deleteMemo :: forall client. (Client === client) =>
              MemoDB
           -> Int
           -> DPrin client
           -> FLAC IO (I client) client ()
deleteMemo store i client = undefined
--deleteMemo store i client = atomically $
--  modifyIFCTVar store $ \store' ->
--  let sealed = M.lookup (Ex client) store' in 
--    withSealed sealed $ \client' (c, sm)
----TODO: HERE
--    (c, M.delete i sm)

-- NOTE: ↓ for documentation
instance ToCapture (Capture "id" Int) where
    toCapture _ = DocCapture "id" "memo id"

instance ToSample Memo where
    toSamples _ = singleSample sampleMemo

instance ToSample [Memo] where
    toSamples _ = singleSample [sampleMemo]

instance ToSample ReqMemo where
    toSamples _ = singleSample $ ReqMemo "Try haskell-servant."

instance ToSample (Lbl Client Memo) where
    toSamples _ = singleSample $ label sampleMemo

instance ToSample (Lbl Client [Memo]) where
    toSamples _ = singleSample $ label [sampleMemo]

instance ToSample () where
    toSamples _ = singleSample ()

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