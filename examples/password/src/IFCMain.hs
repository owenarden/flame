{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module IFCMain where

import Flame.Prelude
import Data.Proxy

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice") 
type Alice = KName "Alice"
bottom = SBot

{- Alice's secret -}
aliceSecret :: Lbl Alice String
aliceSecret = label "secret"

{- A password for protecting that secret -}
password :: Lbl Alice String
password = label "password"

{- | Get the password from the client -}
inputPass :: SPrin client
            -> IFCHandle (I client)
            -> IFCHandle (C client)
            -> IFC IO (I Alice) (I Alice) String
inputPass client stdin stdout = 
  {- Endorse the guess to have Alice's integrity -}
  assume ((client*←) ≽ (alice*←)) $
    reprotect $ hGetLinex (alice*←) stdin
                         
{- | Compare a string to the password -}
chkPass :: SPrin client
        -> String
        -> IFC IO (I Alice) (I Alice) 
           (Maybe (Voice client :≽ Voice Alice, client :≽ Alice))
chkPass client guess =
   {- Declassify the comparison with the password -}
   assume ((bottom*←) ≽ (alice*←)) $
   assume ((bottom*→) ≽ (alice*→)) $ do
   pwd <- liftx (alice*←) password
   protect $ 
     if pwd == guess then
       Just $ ((*∇) client ≽ (*∇) alice, client ≽ alice)
     else
       Nothing
  
secure_main :: DPrin user
        -> IFCHandle (I user)
        -> IFCHandle (C user)
        -> IFC IO (I Alice) SU ()
secure_main userprin stdin stdout =
  let user = (st userprin) in
  let pc = (user*→) *∧ (alice*←) in
  do pass <- inputPass user stdin stdout
     mdel <- chkPass user pass
     case mdel of
       Just (vdel,del) ->
         {- Use the granted authority print Alice's secret -}
         assume vdel $ assume del $ do
           secret <- liftx pc aliceSecret
           hPutStrLnx pc stdout secret
       Nothing ->
         hPutStrLnx pc stdout "Incorrect password."
