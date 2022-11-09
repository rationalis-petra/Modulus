-- | <http://sourceware.org/libffi>.

module Bindings.Libffi where
-- import Foreign
-- import Foreign.C

-- foreign import ccall "ffi_prep_cif" c'ffi_prep_cif
--   :: Ptr C'ffi_cif -> C'ffi_abi -> CUInt -> Ptr C'ffi_type -> Ptr (Ptr C'ffi_type) -> IO C'ffi_status
-- foreign import ccall "&ffi_prep_cif" p'ffi_prep_cif
--   :: FunPtr (Ptr C'ffi_cif -> C'ffi_abi -> CUInt -> Ptr C'ffi_type -> Ptr (Ptr C'ffi_type) -> IO C'ffi_status)

-- foreign import ccall "ffi_call" c'ffi_call
--   :: Ptr C'ffi_cif -> FunPtr (IO ()) -> Ptr () -> Ptr (Ptr ()) -> IO ()
-- foreign import ccall "&ffi_call" p'ffi_call
--   :: FunPtr (Ptr C'ffi_cif -> FunPtr (IO ()) -> Ptr () -> Ptr (Ptr ()) -> IO ())


-- data C'ffi_cif = C'ffi_cif{

--  } deriving (Eq,Show)
-- instance Storable C'ffi_cif where
--   sizeOf _ = 24
--   alignment = sizeOf
--   peek p = do
--     return $ C'ffi_cif
--   poke p (C'ffi_cif) = do
--     return ()


-- type C'ffi_abi = CUInt

-- type C'ffi_arg = CUInt

-- type C'ffi_sarg = CInt

-- type C'ffi_status = CUInt


-- data C'ffi_type = C'ffi_type


-- c'FFI_OK :: (Num a) => a
-- c'FFI_OK = 0

-- c'FFI_BAD_TYPEDEF :: (Num a) => a
-- c'FFI_BAD_TYPEDEF = 1

-- c'FFI_BAD_ABI :: (Num a) => a
-- c'FFI_BAD_ABI = 2

-- c'FFI_FIRST_ABI :: (Num a) => a
-- c'FFI_FIRST_ABI = 0

-- c'FFI_DEFAULT_ABI :: (Num a) => a
-- c'FFI_DEFAULT_ABI = 1

-- c'FFI_LAST_ABI :: (Num a) => a
-- c'FFI_LAST_ABI = 2


-- foreign import ccall "&ffi_type_void" p'ffi_type_void
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_uint8" p'ffi_type_uint8
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_sint8" p'ffi_type_sint8
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_uint16" p'ffi_type_uint16
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_sint16" p'ffi_type_sint16
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_uint32" p'ffi_type_uint32
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_sint32" p'ffi_type_sint32
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_uint64" p'ffi_type_uint64
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_sint64" p'ffi_type_sint64
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_float" p'ffi_type_float
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_double" p'ffi_type_double
--   :: Ptr (C'ffi_type)

-- foreign import ccall "&ffi_type_pointer" p'ffi_type_pointer
--   :: Ptr (C'ffi_type)

