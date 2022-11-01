-- {-# LANGUAGE CApiFFI #-}

module Bindings.Libtdl where


import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
-- import Bindings.Libffi

-- http://www.the-efficient-programmer.com/programming/link-c-lib-in-haskell.html   

  
data OpaqueDlHandle = OpaqueDlHandle
data DSym = DSym

data CModule = CModule { unwrap :: Ptr OpaqueDlHandle }
  deriving Show
type CValue = Ptr DSym

-- Initialisation: returns 0 on success
foreign import ccall "ltdl.h lt_dlinit" dlinit :: IO CInt
foreign import ccall "ltdl.h lt_dlexit" dlexit :: IO CInt

-- Open (import/load) a dynamic module
foreign import ccall "ltdl.h lt_dlopen" dlopen :: CString -> IO (Ptr OpaqueDlHandle)
foreign import ccall "ltdl.h lt_dlopenext" dlopenext :: CString -> IO (Ptr OpaqueDlHandle)

-- loading symbols
foreign import ccall "ltdl.h lt_dlsym" dlsym :: CString -> IO (Ptr DSym)


loadModule :: String -> IO (Maybe CModule)
loadModule str = do
  result <- withCString str dlopenext
  if nullPtr == result then
    pure Nothing
  else
    pure $ Just (CModule result)

