{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module UnifyMe where

import Prelude hiding (print, putStr, putStrLn, getLine)

import Flame.Runtime.IO
import Flame.Principals
import Flame.IFC 
import Data.Proxy

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice")
type Alice = KName "Alice"

aliceSecret :: Lbl Alice String
aliceSecret = label "secret"

unifyMe :: Maybe a -> IO ()
unifyMe ma = let stdout = mkStdout (SBot*→) in
        do _ <- runIFC $
                  case ma of
                    Just a ->
                      {- Use the granted authority print Alice's secret -}
                      assume ((*∇) SBot ≽ (*∇) alice) $ assume (SBot ≽ alice) $
                        ebind aliceSecret $ \secret ->
                        -- this explicit application necessary because GHC does not
                        -- unify variables under implications.
                        -- This restriction means it is safe to unify principal kinded
                        -- type variables based on assume'd givens.
                        -- See infer003, which replaces KBot below with Alice
                        hPutStrLn @_ @Lbl @KBot @(C KBot) @KBot stdout secret
                    Nothing ->             
                        hPutStrLn @_ @Lbl @KBot @(C KBot) @KBot stdout "Incorrect password."
           return ()
