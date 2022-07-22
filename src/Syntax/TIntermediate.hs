module Syntax.TIntermediate where
-- After the intermediate representation
-- we have... the 

import Data(Intermediate(..),
            Expr,
            Object(Type, Function, CConstructor),
            IDefinition(..),
            IPattern(..),
            EvalM,
            Core (CVal),
            Definition(..),
            Arg(..),
            ModulusType(..))

import Data.Environments
import Interpret.Eval(eval)
import Interpret.EvalM (local, fresh_id, throwError)
import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Interpret.Transform
import qualified Interpret.Context as Ctx
import qualified Typecheck.Environment as Env 
import Typecheck.TypeUtils (isLarge)


-- Typed Intermediate Module  
-- The "typed" in typed intermediate beans that all arguments have some kind of
-- type annotation, unlike the 'raw' version. Further, several definitions are
-- toTIntermediate

data IType ty
  = InferType
  | MType ty 
  deriving Show

{-- The two types of binding that can occur within a function are type and val
    bindings. Binding a type means it is available and in scope for subsequent
    types within the body to use, i.e. a ∀a.a --}
data TArg ty
  = BoundArg String ty 
  | ValArg String ty
  | InfArg String Int
  deriving Show


{-- Note: we want module functions to be applicative!!
    this means that type-definitions need to be (able to be) resolved at
    'compile-time', so all created modules have the types be equal. 
    Thus, definitions are realised here with --}
data TDefinition ty
  --             name  type-args id  definitions                   type of variant
  = TVariantDef String [String] Int [(String, Int, [ty])] ty
  | TEffectDef  String [String] Int [(String, Int, [ty])]
  | TSingleDef  String (TIntermediate ty) (Maybe ty)
  | TOpenDef (TIntermediate ty) (Maybe ty)
  deriving Show

data TIntTop ty
  = TExpr (TIntermediate ty)
  | TDefinition (TDefinition ty)
  deriving Show

data TPattern ty
  = TWildCardPat 
  | TBindPat String
  --        id1 id2 sub-patterns  constructor-type
  | TVarPat Int Int [TPattern ty] ty
  deriving Show
  

{-- --}
data TIntermediate ty
  = TValue Expr
  | TSymbol String
  | TApply (TIntermediate ty) (TIntermediate ty)
  | TImplApply (TIntermediate ty) (TIntermediate ty)
  | TModule [TDefinition ty]
  | TSignature [TDefinition ty]
  | TLambda [(TArg ty, Bool)] (TIntermediate ty) (Maybe ty)
  | TIF (TIntermediate ty) (TIntermediate ty) (TIntermediate ty)
  | TAccess (TIntermediate ty) String
  | TMatch (TIntermediate ty) [(TPattern ty, TIntermediate ty)]
  deriving Show



