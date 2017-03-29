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
import GHC.LanguageExtensions.Type


import FastString
import DynFlags
import Outputable

import Control.Monad
import Unsafe.Coerce
import Control.Monad.IO.Class

test = 
 "commit :: FLA m e n => SPrin p -> m e n (I p) (C p) a -> m e n (I p) p a \n\
 \commit p v = assume ((SBot*←) ≽ (p*←)) (reprotect v)"

main :: IO ()
main = do
  (r,t,i) <- defaultErrorHandler defaultFatalMessager defaultFlushOut $
    do runGhc (Just libdir) $
         do result <- load LoadAllTargets
            dflags <- getSessionDynFlags
            let dflags' = dflags { ghcLink      = LinkInMemory
                                 , hscTarget    = HscInterpreted
                                 , packageFlags = [ ExposePackage "-package flame" (PackageArg "flame") $ ModRenaming True [] ]
                                 }
            let dflags'' = xopt_set (xopt_set dflags' PostfixOperators) TypeOperators
            setSessionDynFlags dflags''
            idecls <- sequence $ [ parseImportDecl "import Flame.Principals"
                                 , parseImportDecl "import Flame.IFC"
                                 ]
            -- imports must happen after load
            setContext $ map IIDecl idecls
            -- set plugin after imports, but before runDecls
            setSessionDynFlags dflags'' { pluginModNames = [ (mkModuleName "Flame.Solver") ] }
            [fname] <- runDecls test
            -- At this point we have an evaluation context which has
            -- loaded and compiled the definition of f
            let e = showSDoc dflags'' (pprParenSymName fname)
            --func <- compileExpr e
            -- we also get a representation of
            -- f's type with the following function:
            ty <- exprType e 
            --let f = unsafeCoerce func :: forall a b . a -> b -> a
            -- We have now turned f into a true Haskell value and
            -- coerced its type into the correct type, so now we can
            -- call f normally
            let testCall = ()

            return (result, ty, testCall)
  when (succeeded r) $ pprTrace "Success!" (ppr t <+> ppr (show i)) $ return () --putStrLn $ "Success! "