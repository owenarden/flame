{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}
module Password where

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

chkPass :: Monad e => DPrin client
        -> String
        -> IFC e Alice (I Alice) (Maybe (client :≽ Alice))
chkPass client guess =
   assume (Del (SBot*←) (alice*←)) $
   assume (Del (SBot*→) (alice*→)) $
   lbind password $ \pwd ->
     protectx alice $ 
     if pwd == guess then
       Just $ (st client) ≽ alice
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
main = undefined
--    withPrin (Name "Client") $ \dclient -> 
--      let stdout = mkStdout (dclient^→) in
--      let stdin  = mkStdin (dclient^←) in
--          lbind lpass $ \pass -> 
--            case chkPass dclient dalice pass of
--              Just lDel -> lbind lDel $ \del ->
--                lbind aliceSecret $ \secret -> 
--                      assume del $ hPutStr stdout secret
--              Nothing -> hPutStr stdout "Incorrect password."
