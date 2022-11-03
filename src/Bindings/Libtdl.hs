-- {-# LANGUAGE CApiFFI #-}

module Bindings.Libtdl where

import System.IO.Unsafe (unsafePerformIO)

import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
-- import Bindings.Libffi

-- http://www.the-efficient-programmer.com/programming/link-c-lib-in-haskell.html   

  
data OpaqueDlHandle = OpaqueDlHandle

data CModule = CModule { unwrap :: Ptr OpaqueDlHandle }
  deriving Show
type CValue = FunPtr (CDouble -> CDouble)

-- Initialisation: returns 0 on success
foreign import ccall "ltdl.h lt_dlinit" dlinit :: IO CInt
foreign import ccall "ltdl.h lt_dlexit" dlexit :: IO CInt

-- Open (import/load) a dynamic module
foreign import ccall "ltdl.h lt_dlopen" dlopen :: CString -> IO (Ptr OpaqueDlHandle)
foreign import ccall "ltdl.h lt_dlopenext" dlopenext :: CString -> IO (Ptr OpaqueDlHandle)

-- loading symbols
foreign import ccall "ltdl.h lt_dlsym" dlsym :: (Ptr OpaqueDlHandle) -> CString -> IO (FunPtr a)

foreign import ccall "ltdl.h lt_dlerror" dlerr :: IO CString
-- error message reporting

foreign import ccall "ltdl.h lt_dladdsearchdir" dladdsearchdir :: CString -> IO ()



initModuleLoader :: IO Bool
initModuleLoader = do
  retCode <- dlinit
  if not (retCode < 0) then do
    pure True
  else
    pure False

loadModuleExt :: String -> IO (Either String CModule)
loadModuleExt str = do
  result <- withCString str dlopenext
  if nullPtr == result then do
    cerr <- dlerr
    err <- peekCString cerr
    pure $ Left err
  else
    pure $ Right (CModule result)

loadModuleWithErr :: String -> IO (Either String CModule)
loadModuleWithErr str = do
  result <- withCString str dlopen
  if nullPtr == result then do
    cerr <- dlerr
    err <- peekCString cerr
    pure $ Left err
  else
    pure $ Right (CModule result)

loadModule :: String -> IO (Maybe CModule)
loadModule str = do
  result <- withCString str dlopen
  if nullPtr == result then do
    pure $ Nothing
  else
    pure $ Just (CModule result)

lookupForeignSym :: CModule -> String -> Maybe (FunPtr a)
lookupForeignSym cmodule str = 
  let result = unsafePerformIO $ withCString str (dlsym . unwrap $ cmodule)
  in
    if nullFunPtr == result then
      Nothing
    else
      Just result


foreign import ccall "dynamic"
  mkFun :: FunPtr (CDouble -> CDouble) -> (CDouble -> CDouble)
