-- {-# LANGUAGE CApiFFI #-}

module Bindings.Libtdl where


import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
-- import Bindings.Libffi

-- http://www.the-efficient-programmer.com/programming/link-c-lib-in-haskell.html   

  
data DLib = DLib
data DSym = DSym

type FModule = Ptr DLib

-- Initialisation: returns 0 on success
foreign import ccall "ltdl.h lt_dlinit" dlinit :: IO CInt
foreign import ccall "ltdl.h lt_dlexit" dlexit :: IO CInt

-- Open (import/load) a dynamic module
foreign import ccall "ltdl.h lt_dlopen" dlopen :: CString -> IO (Ptr DLib)

-- loading symbols
foreign import ccall "ltdl.h lt_dlsym" dlsym :: CString -> IO (Ptr DSym)


loadModule :: String -> IO (Ptr DLib)
loadModule = flip withCString dlopen
