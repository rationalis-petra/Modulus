module Syntax.TIntermediate where
-- After the intermediate representation
-- we have... the 

import Data(EvalM,
            Normal,
            Normal'(..),
            Pattern)
import Syntax.Core (Definition(..), Core (..))

import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           IPattern(..),
                           IArg(..))

import Interpret.EvalM (local, fresh_id, throwError)
import Control.Monad.State (State, runState)


-- Typed Intermediate Module  
-- The "typed" in typed intermediate beans that all arguments have some kind of
-- type annotation, unlike the 'raw' version. Further, several definitions are
-- toTIntermediate


{-- The two types of binding that can occur within a function are type and val
    bindings. Binding a type means it is available and in scope for subsequent
    types within the body to use, i.e. a ∀a.a --}
data TArg ty
  = BoundArg String ty
  | InfArg String Int
  | TWildCard ty
  deriving Show


{-- Note: we want module functions to be applicative!!
    this means that type-definitions need to be (able to be) resolved at
    'compile-time', so all created modules have the types be equal. 
    Thus, definitions are realised here with --}
data TDefinition ty
  --            name   id  params         index id  definitions
  = TInductDef String  Int [(String, ty)] ty [(String, Int, ty)]
  | TCoinductDef String Int [(String, ty)] ty [(String, Int, ty)]
  | TSingleDef String (TIntermediate ty) (Maybe ty)
  | TOpenDef (TIntermediate ty) (Maybe ty)
  deriving Show

data TIntTop ty
  = TExpr (TIntermediate ty)
  | TDefinition (TDefinition ty)
  | TAnnotation String (TIntermediate ty) 
  deriving Show

data TPattern ty
  = TWildPat 
  | TBindPat String (Maybe ty)
  | TIMatch Int Int Int ty [TPattern ty]
  | TBuiltinMatch ([Pattern] -> Normal -> (Normal -> Pattern -> EvalM (Maybe [(String, (Normal, Normal))]))
                          -> EvalM (Maybe [(String, (Normal, Normal))]))
    Int ty [TPattern ty]

data TCoPattern ty
  = TCoWildPat 
  | TCoBindPat String (Maybe ty)
  | TCoinductPat String Int Int Int ty [TCoPattern ty]
  deriving Show
  

data TIntermediate ty
  = TValue Normal
  | TSymbol String
  | TApply (TIntermediate ty) (TIntermediate ty)
  | TImplApply (TIntermediate ty) (TIntermediate ty)
  | TStructure [TDefinition ty] (Maybe ty)
  | TSignature [TDefinition ty]
  | TLambda [(TArg ty, Bool)] (TIntermediate ty) (Maybe ty)
  | TProd (TArg ty, Bool) (TIntermediate ty)
  | TIF (TIntermediate ty) (TIntermediate ty) (TIntermediate ty) (Maybe ty)
  | TAccess (TIntermediate ty) String
  | TMatch (TIntermediate ty) [(TPattern ty, TIntermediate ty)] (Maybe ty)
  | TCoMatch [(TCoPattern ty, TIntermediate ty)] (Maybe ty)

  -- TODO: plugins!
  | TAdaptForeign String String [(String, String, ty)] (Maybe ty)
  deriving Show

newtype TIntermediate' = TIntermediate' (TIntermediate TIntermediate')
  deriving Show


instance Show ty => Show (TPattern ty) where
  show (TWildPat) = "TWildPat"
  show (TBindPat sym _) = "TBindPat " <> show sym
  show (TIMatch id1 id2 strip ty pats) = "TIMatch " <> show id1 <> " " <> show id2 <> " " <> show strip
    <> " " <> show ty <> " " <> show pats
  show (TBuiltinMatch _ _ _ pats) = "TBuiltInMatch " <> show pats
