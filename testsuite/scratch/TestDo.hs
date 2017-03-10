{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module TestDo where

import Flame.Runtime.Prelude
import Prelude hiding (fmap, pure, (<*>), return, (>>=), print, putStr, putStrLn, getLine)
import qualified Prelude as M (fmap, pure, (<*>), return, (>>=))
import Debug.Trace
import Control.Monad.IO.Class
import System.Posix.User
import Data.List
import Data.Proxy

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice") -- with GHC 8.0 this is 
type Alice = KName "Alice"

{- Alice's secret -}
aliceSecret :: Lbl Alice String
aliceSecret = label "secret"

{- A password for protecting that secret -}
password :: Lbl Alice String
password = label "password"

{- | Get the password from the client -}
inputPass :: SPrin client
            -> FLAHandle (I client)
            -> FLAHandle (C client)
            -> IFC IO (I Alice) (I Alice) String
inputPass client stdin stdout = 
  {- Endorse the guess to have Alice's integrity -}
  assume ((client*←) ≽ (alice*←)) $
    reprotect $ hGetLine @(I Alice) stdin
                         
{- | Compare a string to the password -}
chkPass :: SPrin client
        -> String
        -> IFC IO (I Alice) (I Alice) 
           (Maybe (Voice client :≽ Voice Alice, client :≽ Alice))
chkPass client guess =
   {- Declassify the comparison with the password -}
   assume ((SBot*←) ≽ (alice*←)) $
   assume ((SBot*→) ≽ (alice*→)) $ do
   pwd <- lift @_ @_ @_ @_ @_ @(I Alice) password
   protect @_ @_ @_ @_ @(I Alice) $ 
     if pwd == guess then
       Just $ ((*∇) client ≽ (*∇) alice, client ≽ alice)
     else
       Nothing
  
secure_main :: forall user. DPrin user
        -> FLAHandle (I user)
        -> FLAHandle (C user)
        -> IFC IO ((C user) ∧ (I Alice)) SU ()
secure_main userprin stdin stdout =
  let user = (st userprin) in
  do pass <- inputPass user stdin stdout
     mdel <- chkPass user pass
     case mdel of
       Just (vdel,del) ->
         {- Use the granted authority print Alice's secret -}
         assume vdel $ assume del $ do
           secret <- lift @_ @_ @_ @_ @_ @((C user) ∧ (I Alice)) aliceSecret
           hPutStrLn @((C user) ∧ (I Alice)) stdout secret
       Nothing ->
         hPutStrLn @((C user) ∧ (I Alice)) stdout "Incorrect password."
