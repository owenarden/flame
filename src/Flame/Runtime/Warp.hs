{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.Warp where
import Network.Wai.Handler.Warp as W
import Network.Wai
import Flame.Principals
import Flame.IFC

run :: IFC m IO n => Port -> Application -> m IO n PT SU ()
run p a = unsafeProtect $ do _ <- W.run p a
                             return $ label ()