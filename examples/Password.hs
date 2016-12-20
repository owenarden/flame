{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

import Prelude hiding (print, putStr, putStrLn, getLine)
import Data.List
import Data.Proxy
import Debug.Trace

import Flame.Runtime.IO
import Flame.Runtime.Principals
import Flame.Principals
import Flame.IFC 

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice")
type Alice = KName "Alice"

{- Alice's secret -}
aliceSecret :: Lbl Alice String
aliceSecret = MkLbl "secret"

{- A password for protecting that secret -}
password :: Lbl Alice String
password = MkLbl "password"

{- | Compare a string to the password -}
chkPass :: Monad e =>
        DPrin client
        -> String
        -> IFC e (I Alice) (I Alice) 
           (Maybe (Voice client :≽ Voice Alice, client :≽ Alice))
chkPass client guess =
   {- Declassify the comparison with the password -}
   assume ((SBot*←) ≽ (alice*←)) $
   assume ((SBot*→) ≽ (alice*→)) $
   lbind password $ \pwd ->
     protectx alice $ 
     if pwd == guess then
       Just $ (SVoice (st client) ≽ SVoice alice, (st client) ≽ alice)
     else Nothing

{- | Get the password from the client -}
inputPass :: DPrin client
            -> FLAHandle (I client)
            -> FLAHandle (C client)
            -> IFC IO (I Alice) (I Alice) String
inputPass client_ stdin stdout = do
      {- Endorse the guess to have Alice's integrity -}
      assume ((st (client_^←)) ≽ (alice*←)) $
        reprotect $ hGetLinex (alice*←) stdin

main :: IO ()
main = withPrin (Name "Client") $ \dclient -> 
        let client_c = ((st dclient)*→) in
        let client_i = ((st dclient)*←) in
        let pc = client_c *∧ (alice*←) in
        let stdout = mkStdout client_c in
        let stdin  = mkStdin client_i in
          do _ <- runIFC $ use (inputPass dclient stdin stdout) $ \pass ->
                           use (chkPass dclient pass) $ \mdel -> 
                             case mdel of
                               Just (vdel,del) ->
                                 {- Use the granted authority print Alice's secret -}
                                 assume vdel $ assume del $
                                   lbind aliceSecret $ \secret ->
                                   hPutStrLnx pc stdout secret
                               Nothing ->
                                 hPutStrLnx pc stdout "Incorrect password."
             return ()
