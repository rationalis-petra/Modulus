{-# LANGUAGE PolyKinds #-}
module Syntax.TIntermediate where
-- After the intermediate representation
-- we have... the 

import Syntax.Normal(Normal(..), Pattern, ArgType)
import Syntax.Core (Definition(..), Core (..))

import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           IPattern(..),
                           IArg(..))


-- Typed Intermediate Module  
-- The "typed" in typed intermediate beans that all arguments have some kind of
-- type annotation, unlike the 'raw' version. Further, several definitions are
-- toTIntermediate


{-- The two types of binding that can occur within a function are type and val
    bindings. Binding a type means it is available and in scope for subsequent
    types within the body to use, i.e. a ∀a.a --}
data TArg m ty
  = BoundArg String (ty m)
  | InfArg String Int
  | TWildCard (ty m)
  deriving Show


{-- Note: we want module functions to be applicative!!
    this means that type-definitions need to be (able to be) resolved at
    'compile-time', so all created modules have the types be equal. 
    Thus, definitions are realised here with --}
data TDefinition m ty
  --            name   id  params         index id  definitions
  = TInductDef String  Int [(String, ty m)] (ty m) [(String, Int, ty m)]
  | TCoinductDef String Int [(String, ty m)] (ty m) [(String, Int, ty m)]
  | TSingleDef String (TIntermediate m ty) (Maybe (ty m))
  | TOpenDef (TIntermediate m ty) (Maybe (ty m))
  deriving Show

data TIntTop m ty
  = TExpr (TIntermediate m ty)
  | TDefinition (TDefinition m ty) 
  | TAnnotation String (TIntermediate m ty)
  deriving Show

data TPattern m (ty :: (* -> *) -> *)
  = TWildPat 
  | TBindPat String (Maybe (ty m))
  | TIMatch Int Int Int (ty m) [TPattern m ty]
  | TBuiltinMatch ([Pattern m] -> Normal m -> (Normal m -> Pattern m -> m (Maybe [(String, (Normal m, Normal m))]))
                               -> m (Maybe [(String, (Normal m, Normal m))]))
    Int (ty m) [TPattern m ty]

data TCoPattern m ty
  = TCoWildPat 
  | TCoBindPat String (Maybe (ty m))
  | TCoinductPat String Int Int Int (ty m) [TCoPattern m ty]
  deriving Show
  

data TIntermediate m ty
  = TValue (Normal m)
  | TSymbol String
  | TApply (TIntermediate m ty) (TIntermediate m ty)
  | TImplApply (TIntermediate m ty) (TIntermediate m ty)
  | TInstanceApply (TIntermediate m ty) (TIntermediate m ty)
  | TStructure [TDefinition m ty] (Maybe (ty m))
  | TSignature [TDefinition m ty]
  | TLambda [(TArg m ty, ArgType)] (TIntermediate m ty) (Maybe (ty m))
  | TProd (TArg m ty, ArgType) (TIntermediate m ty)
  | TIF (TIntermediate m ty) (TIntermediate m ty) (TIntermediate m ty) (Maybe (ty m))
  | TAccess (TIntermediate m ty) String
  | TMatch (TIntermediate m ty) [(TPattern m ty, TIntermediate m ty)] (Maybe (ty m))
  | TCoMatch [(TCoPattern m ty, TIntermediate m ty)] (Maybe (ty m))

  -- TODO: plugins!
  | TAdaptForeign String String [(String, String, ty m)] (Maybe (ty m))
  deriving Show

newtype TIntermediate' m = TIntermediate' (TIntermediate m TIntermediate')
  deriving Show


instance Show (ty m) => Show (TPattern m ty) where
  show (TWildPat) = "TWildPat"
  show (TBindPat sym _) = "TBindPat " <> show sym
  show (TIMatch id1 id2 strip ty pats) = "TIMatch " <> show id1 <> " " <> show id2 <> " " <> show strip
    <> " " <> show ty <> " " <> show pats
  show (TBuiltinMatch _ _ _ pats) = "TBuiltInMatch " <> show pats
