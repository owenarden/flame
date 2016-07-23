{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module Flame.Type.TCB.IFCPtr
where 

import Flame.Type.Principals
import Flame.Type.TCB.IFC

import Foreign.Ptr
import Foreign.ForeignPtr

data IFCPtr (l::KPrin) a = NewIFCPtr { unsafeUnwrap :: ForeignPtr a }

unsafeWithIFCPtr :: IFCPtr l a -> (ForeignPtr a -> IFC IO pc l' b) -> IFC IO pc l' b
unsafeWithIFCPtr p f = f (unsafeUnwrap p)
