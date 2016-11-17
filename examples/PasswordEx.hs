{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

import Prelude hiding (print, putStr, putStrLn, getLine)
import Data.List
import Data.Proxy
import Debug.Trace
import Network.Socket

import Flame.Data.Principals
import Flame.Type.Principals
import Flame.Type.IFC 
import Flame.IO
import System.Posix.User

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice")
type Alice = KName "Alice"

{- Alice's secret -}
aliceSecret :: Lbl Alice String
aliceSecret = label "secret"

{- A password for protecting that secret -}
password :: Lbl Alice String
password = label "password"

{- | Compare a string to the password -}
chkPass :: Monad e =>
        SPrin client
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
       Just $ ((*∇) client ≽ (*∇) alice, client ≽ alice)
     else
       Nothing

{- | Get the password from the client -}
inputPass :: SPrin client
            -> IFCHandle (I client)
            -> IFCHandle (C client)
            -> IFC IO (I Alice) (I Alice) String
inputPass client stdin stdout = do
      {- Endorse the guess to have Alice's integrity -}
      assume ((client*←) ≽ (alice*←)) $
        reprotect $ hGetLinex (alice*←) stdin

main :: IO ()
main = do
      name <- getEffectiveUserName
      withPrin (Name name) $ \client_ -> 
        let client = (st client_) in
        let stdout = mkStdout (client*→) in
        let stdin  = mkStdin (client*←) in
        let pc = (client*→) *∧ (alice*←) in
        do _ <- runIFC $
                use (inputPass client stdin stdout) $ \pass ->
                use (chkPass client pass) $ \mdel -> 
                  case mdel of
                    Just (vdel,del) ->
                      {- Use the granted authority print Alice's secret -}
                      assume vdel $ assume del $
                        lbind aliceSecret $ \secret ->
                        hPutStrLnx pc stdout secret
                    Nothing ->
                      hPutStrLnx pc stdout "Incorrect password."
           return ()
