module Interpret.Structures.BuildStructure where

import Data(Environment(..),
            Normal'(NormMod),
            Normal,
            EvalM)

import Control.Monad.Except (runExcept)
import Data.Text (pack, unpack)

import Parse (parseModule)
import Syntax.Macroexpand
import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           toIntermediate)
import Syntax.Conversions
import Typecheck.Typecheck (typeCheck)
import qualified Typecheck.Context as Ctx
import Interpret.EvalM (local, throwError)
import Interpret.Transform (lift)
import Interpret.Structures.Core
import qualified Interpret.Eval as Eval

import qualified Data.Map as Map


moduleContext = Environment {
  localCtx = Map.empty,
  currentModule = NormMod coreStructure,
  globalModule = NormMod []}

  
buildModule :: Map.Map String Normal -> String -> EvalM Normal
buildModule mp s = 
  case parseModule "internal-module" (pack s) of 
    Left err -> throwError (show err)
    Right ast -> do
      expanded <- local moduleContext (macroExpand ast)
      case toIntermediate expanded moduleContext of 
        Left err -> do 
          throwError err
        Right val -> do
          result <- toTIntermediate val
          (checked, _, _) <- typeCheck result (Ctx.envToCtx moduleContext) 
          core <- case runExcept (toCore checked) of 
            Left err -> throwError err
            Right val -> pure val
          local moduleContext (Eval.eval core)

  
