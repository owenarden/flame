
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Type.Solver #-}

import Flame.Type.Principals
import Flame.Type.IFC
import Flame.Type.Assert

sec :: Lbl KTop String
sec = MkLbl "secret"

main :: IO ()
main = do
    MkLbl str <- return sec
    print str
    
