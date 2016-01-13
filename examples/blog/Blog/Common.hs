{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds, FlexibleInstances, KindSignatures #-}
module Blog.Common where

import Control.Applicative
import Web.Simple
import Web.Simple.Templates

import Control.Monad.IO.Class
import Data.Text.Encoding
import Web.Simple.Templates.Language
import Web.Simple.Controller.Trans
import Flame

data AppSettings = AppSettings {  }

newAppSettings :: IFC PT PT AppSettings
newAppSettings = do
  
  return $ AppSettings

-- TODO: implement
ifc_getTemplate :: FilePath -> IFCController PT PT hs Template
ifc_getTemplate fp = ControllerT $ (\hs r -> do
                       contentsOrErr <- flaReadFile publicTrusted fp
                       case contentsOrErr of
                         Left str -> fail str
                         Right contents ->
                           case compileTemplate . decodeUtf8 $ contents of
                             Left str -> fail str
                             Right tmpl -> return (Right tmpl, hs))

instance HasTemplates (IFC PT PT) AppSettings where
  getTemplate = ifc_getTemplate
  defaultLayout = Just <$> getTemplate "layouts/main.html"

