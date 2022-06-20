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

data IType
  = InferType
  | MType ModulusType 
  deriving Show

{-- The two types of binding that can occur within a function are type and val
    bindings. Binding a type means it is available and in scope for subsequent
    types within the body to use, i.e. a ∀a.a --}
data TArg
  = BoundArg String ModulusType 
  | ValArg String ModulusType
  | InfArg String
  deriving Show


{-- Note: we want module functions to be applicative!!
    this means that type-definitions need to be (able to be) resolved at
    'compile-time', so all created modules have the types be equal. 
    Thus, definitions are realised here with --}
data TDefinition  
  --             name  type-args id  definitions                   type of variant
  = TVariantDef String [String] Int [(String, Int, [ModulusType])] ModulusType
  | TEffectDef  String [String] Int [(String, Int, [ModulusType])]
  | TSingleDef  String TIntermediate (Maybe ModulusType)
  | TOpenDef TIntermediate (Maybe ModulusType)
  deriving Show

data TIntTop
  = TExpr TIntermediate
  | TDefinition TDefinition
  deriving Show

data TPattern
  = TWildCardPat 
  | TBindPat String
  --        id1 id2 sub-patterns constructor-type
  | TVarPat Int Int [TPattern]   ModulusType
  deriving Show
  

{-- --}
data TIntermediate
  = TValue Expr
  | TSymbol String
  | TApply TIntermediate TIntermediate
  | TImplApply TIntermediate TIntermediate
  | TModule [TDefinition]
  | TSignature [TDefinition]
  | TLambda [(TArg, Bool)] TIntermediate (Maybe ModulusType)
  | TIF TIntermediate TIntermediate TIntermediate
  | TAccess TIntermediate String
  | TMatch TIntermediate [(TPattern, TIntermediate)]
  deriving Show



