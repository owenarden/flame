{-# LANGUAGE PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module Main where

import Flame.Data.Principals
import Flame.Type.Principals
import Flame.Type.IFC 
import Flame.IO

import System.IO
import System.Posix.User

import IFCMain

main :: IO ()
main = do
  username <- getEffectiveUserName
  withPrin (Name username) $ \user -> 
    let user' = (st user) in
    let stdin  = mkStdin (user'*←) in
    let stdout = mkStdout (user'*→) in do 
      _ <- runIFC $ secure_main user stdin stdout
      return ()
