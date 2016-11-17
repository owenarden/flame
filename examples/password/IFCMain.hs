{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module IFCMain where

import Flame.Prelude

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
   assume ((SBot*←) ≽ (alice*←)) $
   assume ((SBot*→) ≽ (alice*→)) $ do
   pwd <- liftx (alice*←) password
   protectx (alice*←) $ 
     if pwd == guess then
       Just $ ((*∇) client ≽ (*∇) alice, client ≽ alice)
     else
       Nothing
  
secure_main :: DPrin user
        -> IFCHandle (I user)
        -> IFCHandle (C user)
        -> IFC IO ((C user) ∧ (I Alice)) SU ()
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
