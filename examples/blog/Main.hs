{-# LANGUAGE OverloadedStrings #-}
module Main where

import Application
import Network.Wai.Handler.Warp
import Network.Wai.Middleware.RequestLogger
import System.Environment
import Flame

main :: IO (Lbl PT ())
main = do
  env <- getEnvironment
  let port = maybe 3000 read $ lookup "PORT" env
  runIFC $ app (flaRun publicTrusted publicTrusted port)

