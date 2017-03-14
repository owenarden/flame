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
module MemoDBClient where

import Data.Aeson
import Data.Proxy
import GHC.Generics
import Network.HTTP.Client (newManager, defaultManagerSettings)
import Servant.API hiding (addHeader)
import Servant.Client
import Servant.Client.Experimental.Auth
import Servant.Common.Req 

import qualified MemoDBServer as S (MemoAPI, Memo, MemoClient, MemoServer, ReqMemo(..))
import Data.Text

import Flame.Runtime.Principals
import Flame.IFC
import Flame.TCB.IFC (Lbl(..))
import Flame.Principals
import Flame.Runtime.Time as T
import Control.Concurrent.STM
import Flame.Runtime.STM as F
import qualified Flame.Runtime.Prelude as F hiding (id)
import Flame.Runtime.Sealed
import Data.String
import Control.Monad.IO.Class

import Flame.Runtime.Servant.Auth
import Flame.Runtime.Servant.Auth.Client
import Flame.Runtime.IO as FIO

instance FromJSON S.Memo
instance FromJSON a => FromJSON (Lbl S.MemoClient a) where
  parseJSON v = UnsafeMkLbl <$> (parseJSON v)

type instance AuthClientData (AuthProtect "cookie-auth") = Text
authenticateAs :: Text -> AuthenticateReq (AuthProtect "cookie-auth")
authenticateAs s = mkAuthenticateReq s (\s -> addHeader "servant-auth-cookie" s)

memoApi :: Proxy S.MemoAPI
memoApi = Proxy

--
-- TODO: Missing IFC checks
--
getMemos :: AuthenticateReq (AuthProtect "cookie-auth")
         -> FLAC ClientM (I S.MemoClient) S.MemoClient [S.Memo]

postMemo :: AuthenticateReq (AuthProtect "cookie-auth")
         -> S.ReqMemo
         -> FLAC ClientM S.MemoClient S.MemoClient S.Memo

deleteMemo :: AuthenticateReq (AuthProtect "cookie-auth")
           -> Int
           -> FLAC ClientM (I S.MemoClient) S.MemoClient ()

getMemos :<|> postMemo :<|> deleteMemo = client memoApi

runFLACClientM m env = runClientM (runFLAC m) env
stdout = mkStdout $ secretUntrusted

--unsafePerformFLACIO m = unsafeProtect $ UnsafeMkLbl <$> liftIO m

queries :: FLAC ClientM S.MemoClient S.MemoClient ()
queries =
  use (getMemos (authenticateAs "key1")) $ \memos ->
  apply (FIO.liftIO $ hPutStr stdout "GET key1 before POST: ") $ \_ ->
  apply (FIO.liftIO $ hPrint stdout memos) $ \_ ->
  apply (postMemo (authenticateAs "key1") (S.ReqMemo "Try Haskell servant.")) $ \_ ->
  use (getMemos (authenticateAs "key1")) $ \memos' ->
  FIO.liftIO $ apply (hPutStr stdout "GET key1 after POST: ") $ \_ ->
  FIO.liftIO $ hPrint stdout memos'

run :: IO ()
run = do
  manager <- newManager defaultManagerSettings
  res <- runFLACClientM queries (ClientEnv manager (BaseUrl Http "localhost" 8080 ""))
  case res of
    Left err -> putStrLn $ "Error: " ++ show err
    Right qs -> return ()
