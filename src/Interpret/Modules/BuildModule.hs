module Interpret.Modules.BuildModule where

import Data(Context,
            Object(Module),
            Expr,
            EvalM,
            IDefinition(..),
            ValContext(..),
            Intermediate(..))

import Control.Monad.Except (throwError)
import Data.Text (pack, unpack)

import Parse (parseModule)
import Syntax.Macroexpand
import Syntax.Intermediate
import Interpret.Eval (eval)
import Interpret.EvalM (local)
import Interpret.Transform (lift)
import Interpret.Modules.Core

import qualified Data.Map as Map


moduleContext = ValContext {
  localCtx = Map.empty,
  currentModule = Module coreModule,
  globalModule = Module Map.empty}

  
buildModule :: Map.Map String Expr -> String -> EvalM Expr
buildModule mp s = 
  case parseModule "internal-module" (pack s) of 
    Left err -> lift $ throwError (show err)
    Right ast -> do
      expanded <- local moduleContext (macroExpand ast)
      case toIntermediate expanded moduleContext of 
        Left err -> do 
          lift $ throwError err
        Right val -> 
          local moduleContext (eval val)
        --     (eval (IModule (Map.foldrWithKey
        --                   (\k v m -> (ISingleDef k (IValue v)) : m) m mp)))
        -- Right (ISignature m) -> 
        --   local moduleContext
        --     (eval (ISignature (Map.foldrWithKey
        --                   (\k v m -> (ISingleDef k (IValue v)) : m) m mp)))

        -- Right val -> do
        --   tint <- toTIntermediateTop val (toEnv moduleContext)
        --   case runCheckerTop tint (toEnv moduleContext) of 
        --     Right res -> do
        --       tint <- case res of
        --         Left (tint, ty) -> do
        --           print ty
        --           pure tint
        --         Right tint -> pure tint
        --       case runExcept (Core.toTopCore tint)
        --         Right v -> do 
        --           ()
                
        -- Right _ -> 
        --   lift $ throwError "build module did not receive module"

  
