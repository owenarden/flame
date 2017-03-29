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
import Servant ((:>), (:<|>)(..), ReqBody, Capture, Get, Post, Delete, Proxy(..), Server, serve, ServantErr, HasServer(..), reflectMethod, ReflectMethod(..), serveDirectoryFileServer)
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
import Data.Text                        (Text, pack, unpack)
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

import Flame.Servant
import Flame.Servant.Server

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

-- JS stuff
import qualified Data.Text.IO as TextIO
import Servant.Foreign
import Servant.JS
import qualified Language.Javascript.JQuery
import Control.Lens hiding (use, Context)


-- GHC stuff
import GHC
import GHC.Paths (libdir)
import Module
import GHC
import Packages
import GhcMonad
import Outputable
import System.Environment
import DynFlags
import Module
import BasicTypes
import GHC.LanguageExtensions.Type
import FastString
import DynFlags
import Outputable
import Control.Monad
import Unsafe.Coerce
import Control.Monad.IO.Class

{- Auth specific -}
type Alice = KName "Alice"
alice = Name "Alice"

type Bob = KName "Bob"
bob = Name "Bob"

type Carol = KName "Carol"
carol = Name "Carol"

-- | A database mapping keys to users.
prin_database :: FLAC IO (I EvalServer) EvalServer (Map ByteString Prin)
prin_database = protect $ fromList [ ("key1", alice)
                                   , ("key2", bob)
                                   , ("key3", carol)
                                   ]

lookupPrin :: ByteString -> FLAC IO (I EvalServer) (I EvalServer) Prin
lookupPrin key = 
  assume2 (SConf SBot ≽ SConf (st $ appServer evalAPI)) $
   use prin_database $ \database ->
    case Map.lookup key database of
      Nothing ->  protect $ undefined --throwError (err403 { errBody = "Invalid Cookie" })
      Just usr -> protect $ usr
                                
-- | A method that, when given a password, will return a Prin.
-- This is our bespoke (and bad) authentication logic.
authenticate :: ByteString -> Handler (FLAC IO (I EvalServer) (I EvalServer) EvalAuth)
authenticate key = return $ use (lookupPrin key) $ \usr -> 
                    withPrin @(FLAC IO (I EvalServer) (I EvalServer) EvalAuth) usr $ \client ->
                    let sclient = st client in
                     assume2 (apiAppServer ≽ (sclient *∧ (*∇) sclient)) $
                      assume2 (apiClient ≽ sclient) $ assume2 (sclient ≽ apiClient) $
                       protect $ authorize client
  where
    apiAppServer = st $ appServer evalAPI
    apiClient    = st $ currentClient evalAPI

-- | The auth handler wraps a function from Request -> Handler Prin
-- we look for a Cookie and pass the value of the cookie to `lookupPrin`.
authHandler :: AuthHandler Request (FLAC IO (I EvalServer) (I EvalServer) EvalAuth)
authHandler =
  let handler req = case lookup "servant-auth-cookie" (requestHeaders req) of
        Nothing -> throwError (err401 { errBody = "Missing auth header" })
        Just authCookieKey -> authenticate authCookieKey
  in mkAuthHandler handler


-- | We need to specify the data returned after authentication
type instance AuthServerData (AuthProtect "cookie-auth") = FLAC IO (I EvalServer) (I EvalServer) EvalAuth

data ReqCode = ReqCode { code :: Text } deriving (Show, Generic)

instance FromJSON ReqCode
instance ToJSON ReqCode

type EvalAPI =
    "eval" :> AuthProtect "cookie-auth"
          :> ReqBody '[JSON] ReqCode
          :> EnforceFLA (I EvalClient) (I EvalClient) (Post '[JSON] Bool) 

evalAPI :: Proxy EvalAPI
evalAPI = Proxy

type EvalAPI_Raw = EvalAPI :<|> Raw
evalAPI_Raw :: Proxy EvalAPI_Raw
evalAPI_Raw = Proxy

type EvalAuth = IFCAuth EvalAPI

-- | The context that will be made available to request handlers. We supply the
-- "cookie-auth"-tagged request handler defined above, so that the 'HasServer' instance
-- of 'AuthProtect' can extract the handler and run it on the request.
genAuthServerContext :: Context (AuthHandler Request (FLAC IO (I EvalServer) (I EvalServer) EvalAuth) ': '[])
genAuthServerContext = authHandler :. EmptyContext

apiJS :: Text
apiJS = jsForAPI evalAPI jquery

instance (HasForeignType lang ftype Text, HasForeign lang ftype api)
  => HasForeign lang ftype (AuthProtect "cookie-auth" :> api) where
  type Foreign ftype (AuthProtect "cookie-auth" :> api) = Foreign ftype api

  foreignFor lang Proxy Proxy req =
    foreignFor lang Proxy subP $ req & reqHeaders <>~ [HeaderArg arg]
    where
      hname = "servant-auth-cookie"
      arg   = Arg
        { _argName = PathSegment hname
        , _argType  = typeFor lang (Proxy :: Proxy ftype) (Proxy :: Proxy Text) }
      subP  = Proxy :: Proxy api


writeJS :: IO ()
writeJS = do
  TextIO.writeFile "html/api.js" apiJS
  jq <- TextIO.readFile =<< Language.Javascript.JQuery.file
  TextIO.writeFile "html/jq.js" jq

main :: IO ()
main = do
    args <- getArgs
    case args of
 --       ["d"] -> putStrLn doc
        ["s"] -> writeJS >> runApp
        _     -> putStrLn "unknown option"

runApp :: IO ()
runApp = do 
  run 8080 $ app

app :: Application
app = serveWithContext evalAPI_Raw genAuthServerContext $ (server :<|> serveDirectoryFileServer "html")

type EvalServer = KTop
type EvalClient = KName "EvalClient"

{- common defs -}
instance IFCApp EvalAPI where
  type AppServer EvalAPI = EvalServer
  type Client EvalAPI = EvalClient
  
  appServerPrin = const $ Top
  appServerTy   = const $ STop

  currentClientPrin = const $ Name "EvalClient"
  currentClientTy   = const $ SName (Proxy :: Proxy "EvalClient")

server :: Server EvalAPI
server = evalH
  where
    apiEvalClient = currentClient evalAPI
    apiEvalServer = appServer evalAPI
    mkSig client = (dyn (client^←), dyn (client^←))

    evalH :: FLAC IO (I EvalServer) (I EvalServer) EvalAuth
              -> ReqCode
              -> FLAC Handler (I EvalClient) (I EvalClient) Bool
    evalH auth r = mkHandler evalAPI auth mkSig (apiEvalClient^←) (apiEvalClient^←) $
       \(client :: DPrin client) pc' l' -> do
            Equiv <- pc' `eq` (client^←)
            Equiv <- l' `eq` (client^←)
            return (Equiv, Equiv, reprotect $ eval client r)

eval_pre = "String -> FLAC IO (I Bearer)"

eval :: forall client. DPrin client
         -> ReqCode
         -> FLAC IO (I client) (I client) Bool
eval client req =
   let src = unpack (code req) in unsafeProtect $ do
     (r,t,i) <- defaultErrorHandler defaultFatalMessager defaultFlushOut $
       do runGhc (Just libdir) $
            do result <- load LoadAllTargets
               dflags <- getSessionDynFlags
               let dflags' = dflags { ghcLink      = LinkInMemory
                                    , hscTarget    = HscInterpreted
                                    , packageFlags = [ ExposePackage "-package flame" (PackageArg "flame") $ ModRenaming True [] ]
                                    }
               let dflags'' = xopt_set (xopt_set dflags' PostfixOperators) TypeOperators
               setSessionDynFlags dflags''
               idecls <- sequence $ [ parseImportDecl "import Flame.Principals"
                                    , parseImportDecl "import Flame.IFC"
                                    ]
               -- imports must happen after load
               setContext $ map IIDecl idecls
               -- set plugin after imports, but before runDecls
               setSessionDynFlags dflags'' { pluginModNames = [ (mkModuleName "Flame.Solver") ] }
               [fname] <- runDecls src
               -- At this point we have an evaluation context which has
               -- loaded and compiled the definition of f
               let e = showSDoc dflags'' (pprParenSymName fname)
               --func <- compileExpr e
               -- we also get a representation of
               -- f's type with the following function:
               ty <- exprType e 
               --let f = unsafeCoerce func :: forall a b . a -> b -> a
               -- We have now turned f into a true Haskell value and
               -- coerced its type into the correct type, so now we can
               -- call f normally
               let testCall = ()

               return (result, ty, testCall)
     return $ label (succeeded r)

instance (ToAuthInfo (AuthProtect "cookie-auth"), HasDocs api) => HasDocs (AuthProtect "cookie-auth" :> api) where
  docsFor Proxy (endpoint, action) =
    docsFor (Proxy :: Proxy api) (endpoint, action')
      where
        authProxy = Proxy :: Proxy (AuthProtect "cookie-auth")
        action' = over authInfo (|> toAuthInfo authProxy) action

instance ToAuthInfo (AuthProtect "cookie-auth") where
  toAuthInfo p = DocAuthentication "servant-auth-cookie" "A key in the principal database"
