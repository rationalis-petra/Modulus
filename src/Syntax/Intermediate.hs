module Syntax.Intermediate where
{-- The Intermediate module is for converting a macro-expanded AST into an
    intermediate representation that can then be interpreted or compiled
--}

import Prelude hiding (lookup)

import Control.Monad.Except (Except, runExcept) 
import qualified Data.Set as Set

import Bindings.Libtdl (CModule)
  
import qualified Interpret.Environment as Env
import Syntax.Normal (AST(..),
                      Environment,
                      Special(..),
                      Normal(Symbol, Special, Keyword, NormIVal),
                      Neutral)


-- arguments to functions may have optional type annotations
data IArg m
  = Sym String
  | Annotation String (Intermediate m)
  | IWildCardArg (Intermediate m)
  deriving Show


data IDefinition m
  = ISingleDef String (Intermediate m) (Maybe (Intermediate m))
  | IInductDef String [IArg m] (Intermediate m) [(String, Intermediate m)]
  | ICoinductDef String [IArg m] (Intermediate m) [(String, Intermediate m)]
  | IEffectDef String [String] [(String, [Intermediate m])]
  | IOpenDef (Intermediate m)
  deriving Show

-- Untyped (typed) intermediate
data Intermediate m
  = IValue (Normal m)
  | IDefinition (IDefinition m)
  | IApply (Intermediate m) (Intermediate m)
  | IImplApply (Intermediate m) (Intermediate m)
  | IQuote (AST m)
  | IAccess (Intermediate m) String
  | IIF (Intermediate m) (Intermediate m) (Intermediate m)
  | ISymbol String
  | ILet [(String, Intermediate m)] (Intermediate m)
  | ILetOpen [Intermediate m] (Intermediate m)
  | ILambda [(IArg m, Bool)] (Intermediate m)
  | IProd (IArg m, Bool) (Intermediate m)
  | IMacro [IArg m] (Intermediate m)
  | IStructure [IDefinition m] 
  | ISignature [IDefinition m] 
  | IMatch (Intermediate m) [(IPattern m, Intermediate m)]
  | ICoMatch [(ICoPattern m, Intermediate m)]
  | IAnnotation String (Intermediate m)

  -- TODO: plugin system!!
  | IAdaptForeign String String [(String, String, Intermediate m)]
  deriving Show

data IPattern m
  = ISingPattern String
  | IWildCard
  | ICheckPattern (Intermediate m) [IPattern m]
  deriving Show

data ICoPattern m
  = ICoSingPattern String
  | ICoWildCard
  | ICoCheckPattern (Intermediate m) [ICoPattern m]
  deriving Show
