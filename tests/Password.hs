{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

import Prelude hiding (print, putStr, putStrLn, getLine)
import Data.List
import Data.Proxy
import Debug.Trace
import Network.Socket

import Flame.Data.Principals
import Flame.Type.Principals
import Flame.Type.IFC 
import Flame.IO

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice")
type Alice = KName "Alice"

aliceSecret :: Lbl Alice String
aliceSecret = MkLbl "secret"

password :: Lbl Alice String
password = MkLbl "jbixkt"

chkPass :: Monad e =>
        DPrin client
        -> String
        -> IFC e Alice (I Alice) 
           (Maybe (Voice client :≽ Voice Alice, client :≽ Alice))
chkPass client guess =
   assume ((SBot*←) ≽ (alice*←)) $
   assume ((SBot*→) ≽ (alice*→)) $
   lbind password $ \pwd ->
     protectx alice $ 
     if pwd == guess then
       Just $ (SVoice (st client) ≽ SVoice alice, (st client) ≽ alice)
     else Nothing

getPassword :: DPrin client
            -> IFCHandle (I client)
            -> IFCHandle (C client)
            -> IO (Lbl (I Alice) String)
getPassword client_ stdin stdout = do
      guess <- runIFC $ hGetLine stdin
      runIFCx (alice*←) $ assume ((st (client_^←)) ≽ (alice*←)) $
                                  lift $ relabel guess

main :: IO ()
main = withPrin (Name "Client") $ \dclient -> 
        let client_c = ((st dclient)*→) in
        let client_i = ((st dclient)*←) in
        let pc = client_c *∧ (alice*←) in
        let stdout = mkStdout client_c in
        let stdin  = mkStdin client_i in
        do pass <- getPassword dclient stdin stdout 
           ldel <- runIFC $ lbind pass $ chkPass dclient
           _    <- runIFC $ lbind ldel $ \mdel -> 
                    case mdel of
                      Just (vdel,del) -> assume vdel $ assume del $
                                         lbind aliceSecret $ \secret -> 
                                           hPutStrLnx pc stdout secret
                      Nothing -> hPutStrLnx pc stdout "Incorrect password."
           return ()
