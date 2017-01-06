{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

import Prelude hiding (print, putStr, putStrLn, getLine)
import Data.List
import Data.Proxy
import Debug.Trace

import Flame.Runtime.IO
import Flame.Runtime.Principals
import Flame.Principals
import Flame.IFC 
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
chkPass :: (Monad e, I a ≽ Voice a) =>
        SPrin client
        -> SPrin a
        -> Lbl a String
        -> String
        -> IFC e (I a) (I a) 
           (Maybe (Voice client :≽ Voice a, client :≽ a))
chkPass client a password guess =
   {- Declassify the comparison with the password -}
   assume ((SBot*←) ≽ (a*←)) $
   assume ((SBot*→) ≽ (a*→)) $
   ebind password $ \pwd ->
     protect $ 
     if pwd == guess then
       Just $ ((*∇) client ≽ (*∇) a, client ≽ a)
     else
       Nothing
{- | Get the password from the client -}
inputPass :: SPrin client
            -> FLAHandle (I client)
            -> FLAHandle (C client)
            -> IFC IO (I Alice) (I Alice) String
inputPass client stdin stdout = do
      {- Endorse the guess to have Alice's integrity -}
      assume ((client*←) ≽ (alice*←)) $
        reprotect $ hGetLine stdin

main :: IO ()
main = do
      name <- getEffectiveUserName
      withPrin (Name name) $ \(client_ :: DPrin client) -> 
        let client = (st client_) in
        let stdout = mkStdout (client*→) in
        let stdin  = mkStdin (client*←) in
        do _ <- runIFC $
                use (inputPass client stdin stdout) $ \pass ->
                use (chkPass client alice aliceSecret pass) $ \mdel -> 
                  case mdel of
                    Just (vdel,del) ->
                      {- Use the granted authority print Alice's secret -}
                      assume vdel $ assume del $
                        ebind aliceSecret $ \secret ->
                        -- why is this explicit application necessary?
                        hPutStrLn @_ @(C client) stdout secret
                    Nothing ->
                      hPutStrLn @_ @(C client) stdout "Incorrect password."
           return ()
