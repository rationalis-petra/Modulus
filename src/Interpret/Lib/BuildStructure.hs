module Interpret.Lib.BuildStructure where

import Data(Environment(..),
            Normal'(NormSct, NormSig),
            Normal,
            EvalM,
            toEmpty)

import Control.Monad.Except (runExcept)
import Data.Text (pack, unpack)

import Parse (parseScript)
import Syntax.Macroexpand
import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..))
import Syntax.Conversions
import Typecheck.Typecheck (typeCheck)
import Interpret.EvalM (local, throwError)
import Interpret.Lib.Core
import qualified Interpret.Eval as Eval

import qualified Data.Map as Map


moduleContext = Environment {
  localCtx = Map.empty,
  currentModule = NormSct (toEmpty coreTerms) (NormSig []),
  globalModule = NormSct [] (NormSig [])}
