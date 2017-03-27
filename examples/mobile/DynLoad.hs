{-# language RankNTypes #-}
import GHC
import GHC.Paths (libdir)
import Module
import GHC
import Packages
import GhcMonad
import Outputable
import System.Environment
import DynFlags
import Module
import BasicTypes
import Language.Haskell.TH.LanguageExtensions


import FastString
import DynFlags
import Outputable

import Control.Monad
import Unsafe.Coerce
import Control.Monad.IO.Class

test = "f x y = Flame.Principals.SBot"
--  "commit :: FLA m e n => SPrin p -> m e n (I p) (C p) a -> m e n (I p) p a \n\
--   \commit p v = assume ((SBot*←) ≽ (p*←)) (reprotect v)"

main :: IO ()
main = do
  (r,t,i) <- defaultErrorHandler defaultFatalMessager defaultFlushOut $
    do runGhc (Just libdir) $
         do dflags <- getSessionDynFlags
            let dflags' = dflags { ghcLink    = LinkInMemory
                                 , hscTarget  = HscInterpreted
                                 , packageFlags = [ ExposePackage "-package flame" (PackageArg "flame") $ ModRenaming True [] ]
                                 --, packageFlags = [ ExposePackage "-package ghc" (PackageArg "ghc") $ ModRenaming True [] ]
                                 --, pluginModNames = [ (mkModuleName "Flame.Solver") ] 
                                 --, extensions 
                                 }
            setSessionDynFlags dflags'
            dflags2 <- getSessionDynFlags
            dflags3 <- liftIO $ interpretPackageEnv dflags2
            --_ <- liftIO $ initPackages dflags2
            mod <- lookupModule (mkModuleName "Flame.Principals") (Just $ mkFastString "flame")
            result <- load LoadAllTargets
            idecl <- parseImportDecl "import Flame.Principals"
            setContext [IIDecl idecl]
            [fname] <- runDecls test
            -- At this point we have an evaluation context which has
            -- loaded and compiled the definition of f

            let e = showSDoc dflags2 (pprParenSymName fname)
            func <- compileExpr e
            -- we also get a representation of
            -- f's type with the following function:
            ty <- exprType e 
            let f = unsafeCoerce func :: forall a b . a -> b -> a
            -- We have now turned f into a true Haskell value and
            -- coerced its type into the correct type, so now we can
            -- call f normally
            let testCall = f 3 2

            return (result, ty, testCall)
  when (succeeded r) $ pprTrace "Success!" (ppr t <+> ppr (show i)) $ return () --putStrLn $ "Success! " 
