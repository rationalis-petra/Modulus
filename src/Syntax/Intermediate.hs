module Syntax.Intermediate where
{-- The Intermediate module is for converting a macro-expanded AST into an
    intermediate representation that can then be interpreted or compiled
--}

import Prelude hiding (lookup)

import Control.Monad.Except (Except, runExcept) 
import qualified Data.Set as Set
import qualified Interpret.Environment as Env
import Data (AST(..),
             Environment,
             Special(..),
             Normal,
             Normal'(Symbol, Special, Keyword, NormIVal),
             Neutral,
             Neutral')



-- arguments to functions may have optional type annotations
data IArg
  = Sym String
  | Annotation String Intermediate
  | IWildCardArg Intermediate
  deriving Show


data IDefinition
  = ISingleDef String Intermediate (Maybe Intermediate)
  | IInductDef String [IArg] Intermediate [(String, Intermediate)]
  | ICoinductDef String [IArg] Intermediate [(String, Intermediate)]
  | IEffectDef String [String] [(String, [Intermediate])]
  | IOpenDef Intermediate
  deriving Show

-- Untyped (typed) intermediate
data Intermediate
  = IValue Normal
  | IDefinition IDefinition
  | IApply Intermediate Intermediate
  | IImplApply Intermediate Intermediate
  | IQuote AST
  | IAccess Intermediate String
  | IDo [Intermediate]
  | IIF Intermediate Intermediate Intermediate
  | ISymbol String
  | ILet [(String, Intermediate)] Intermediate
  | ILetOpen [Intermediate] Intermediate
  | ILambda [(IArg, Bool)] Intermediate
  | IProd (IArg, Bool) Intermediate
  | IMacro [IArg] Intermediate
  | IStructure [IDefinition] 
  | ISignature [IDefinition] 
  | IHandle Intermediate [(String, [String], Intermediate)]
  | IMkHandler [(String, [String], Intermediate)]
  | IHandleWith Intermediate Intermediate
  | IMatch Intermediate [(IPattern, Intermediate)]
  | ICoMatch [(ICoPattern, Intermediate)]
  | IAnnotation String Intermediate
  deriving Show

data IPattern
  = ISingPattern String
  | IWildCard
  | ICheckPattern Intermediate [IPattern]
  deriving Show

data ICoPattern
  = ICoSingPattern String
  | ICoWildCard
  | ICoCheckPattern Intermediate [ICoPattern]
  deriving Show
