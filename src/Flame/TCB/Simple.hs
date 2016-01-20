module Flame.TCB.Simple where

import Flame.TCB.Core
import Control.Monad
import Control.Monad.IO.Class

import Network.Wai 
import Network.Wai.Handler.Warp as Warp

import qualified Data.ByteString as S

import Web.Simple.Controller.Trans

--type IFCApplication pc l = Bound pc -> Bound l -> IFC pc l Request
--                      -> (IFC pc l Response -> IFC pc l ResponseReceived)
--                      -> IFC pc l ResponseReceived
--type IFCController pc l s = Bound pc -> Bound l -> ControllerT s (IFC pc l)
--
-- TODO: move network stuff to Flame.Simple and Flame.Network.Wai
-- TODO: move IO stuff to 

--flaPutStrLn :: (FlowsTo l lblout, FlowsTo pc lblout) => IFC pc l String -> IFC lblout l' ()
--flaPutStrLn str = UnsafeIFC $ do
--                               s <- runIFC str 
--                               u <- putStrLn $ unsafeRunLbl s 
--                               return (MkLbl u)

{- Dynamically check whether file has label fileLbl -}
--checkFileLbl :: SPrin fileLbl -> FilePath -> Bool
---- TODO: implement
--checkFileLbl lbl fp = True
--
--readFile :: Bound fileLbl -> FilePath -> IFC pc fileLbl (Either String S.ByteString)
--readFile lbl fp = UnsafeIFC $ if checkFileLbl (dyn lbl) fp
--                                  then do 
--                                    u <- S.readFile fp
--                                    return (MkLbl (Right u))
--                                  else 
--                                    return (MkLbl (Left "Access check failed"))
--
--unsafeUnlabelApp :: IFCApplication pc l -> Application
--unsafeUnlabelApp app req responseFunc = do 
--            resp <- runIFC (app req (UnsafeIFC . (\resp -> do
--                                                             r <- responseFunc resp
--                                                             return (MkLbl r))))
--            return $ unsafeRunLbl $ resp
--  
--run :: Bound pc -> Bound l -> Port -> IFCApplication pc l -> IFC pc l () 
--run pc l port app = UnsafeIFC $ do
--                                     Warp.run port (unsafeUnlabelApp app);
--                                     return (MkLbl ())
--
--
