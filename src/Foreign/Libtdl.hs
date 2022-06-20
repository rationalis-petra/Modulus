{-# LANGUAGE CApiFFI #-}

module Foreign.Libtdl where


import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
-- import Bindings.Libffi

-- http://www.the-efficient-programmer.com/programming/link-c-lib-in-haskell.html   

  
data DLib = DLib

foreign import capi "ltdl.h lt_dlinit" dlinit :: IO CInt

foreign import capi "ltdl.h lt_dlexit" dlexit :: IO CInt

foreign import capi "ltdl.h lt_dlopen" dlopen :: CString -> IO (Ptr DLib)
