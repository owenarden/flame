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
module ServantClient where

import Data.Aeson
import Data.Proxy
import GHC.Generics
import Network.HTTP.Client (newManager, defaultManagerSettings)
import Servant.API hiding (addHeader)
import Servant.Client
import Servant.Client.Experimental.Auth
import Servant.Common.Req 

import qualified ServantAuth as S (MemoAPI, Memo, Client, AppServer, ReqMemo(..))
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

instance FromJSON S.Memo
instance FromJSON a => FromJSON (Lbl S.Client a) where
  parseJSON v = UnsafeMkLbl <$> (parseJSON v)

type instance AuthClientData (AuthProtect "cookie-auth") = Text
authenticateAs :: Text -> AuthenticateReq (AuthProtect "cookie-auth")
authenticateAs s = mkAuthenticateReq s (\s -> addHeader "servant-auth-cookie" s)

memoApi :: Proxy S.MemoAPI
memoApi = Proxy

primGetMemos :: AuthenticateReq (AuthProtect "cookie-auth") -> ClientM (Lbl S.Client [S.Memo])
primPostMemo :: AuthenticateReq (AuthProtect "cookie-auth") -> S.ReqMemo -> ClientM (Lbl S.Client S.Memo)
primDeleteMemo :: AuthenticateReq (AuthProtect "cookie-auth") -> Int -> ClientM (Lbl S.Client ())
primGetMemos :<|> primPostMemo :<|> primDeleteMemo = client memoApi

--
-- TODO: Missing IFC checks
--
getMemos :: AuthenticateReq (AuthProtect "cookie-auth")
         -> FLACClientM (I S.Client) S.Client [S.Memo]
getMemos r = unsafeProtect (primGetMemos r)

postMemo :: AuthenticateReq (AuthProtect "cookie-auth")
         -> S.ReqMemo
         -> FLACClientM (I S.Client) S.Client S.Memo
postMemo r m = unsafeProtect (primPostMemo r m)

deleteMemo :: AuthenticateReq (AuthProtect "cookie-auth")
           -> Int
           -> FLACClientM (I S.Client) S.Client ()
deleteMemo r i = unsafeProtect (primDeleteMemo r i)

type FLACClientM a b c = FLAC ClientM a b c

runFLACClientM m env = runClientM (runFLAC m) env
unsafePerformFLACIO m = unsafeProtect $ UnsafeMkLbl <$> liftIO m

queries :: FLACClientM (I S.Client) S.Client ()
queries =
  use (getMemos (authenticateAs "key1")) $ \memos ->
  use (unsafePerformFLACIO (putStr "GET key1: " >> print memos)) $ \_ ->
  use (postMemo (authenticateAs "key1") (S.ReqMemo "Try Haskell servant.")) $ \_ ->
  use (getMemos (authenticateAs "key1")) $ \memos' ->
  unsafePerformFLACIO (putStr "GET key1 after POST: " >> print memos')

run :: IO ()
run = do
  manager <- newManager defaultManagerSettings
  res <- runFLACClientM queries (ClientEnv manager (BaseUrl Http "localhost" 8080 ""))
  case res of
    Left err -> putStrLn $ "Error: " ++ show err
    Right qs -> return ()
