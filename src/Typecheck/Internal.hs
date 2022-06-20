module Typecheck.Internal where

import qualified Data.Map as Map

-- the type-representation used /internally/: within the typechecking module
-- data IType
--   = TypeN Int
--   -- Left str  -> "solidified" type variable, e.g. as written by a user.
--   -- Right int -> currently being inferred
--   | MVar (Either String Int)
--   | Signature (Map.Map String IType)
--   | MArr IType IType
--   | MDep IType String IType
--   | ImplMDep IType String IType
--   | MDot IType String

--   -- "Primitive" / native types
--   | MPrim PrimType
--   | MNamed Int String [IType] 
--   | MList IType
--   | MVector IType
--   -- TODO: effect types

--   -- BAD -> we want him gone!
--   | Undef
--   | Large
--   deriving Eq
