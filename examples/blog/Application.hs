{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds, FlexibleInstances, FlexibleContexts, KindSignatures #-}
module Application where

import Blog.Common
import Web.Simple
import Web.Simple.Templates
import Data.Aeson
import Web.Simple.Controller.Trans as T

import Flame

-- | Convert the controller into an 'Application'
flaControllerApp :: s -> IFCController PT PT s a -> IFCApplication PT PT
flaControllerApp s ctrl req responseFunc = do
  resp <- T.controllerApp s ctrl req
  responseFunc resp

app :: (IFCApplication PT PT -> IFC PT PT ()) -> IFC PT PT ()
app runner = do
  settings <- newAppSettings
  runner $ flaControllerApp settings $ do
    T.routeTop $ render "index.html" ()
    -- TODO: routes go here
