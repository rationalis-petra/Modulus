module Interpret.Modules.BuildModule where

import Data(Environment(..),
            Value(Module),
            Expr,
            EvalM,
            IDefinition(..),
            Intermediate(..))

import Control.Monad.Except (runExcept)
import Data.Text (pack, unpack)

import Parse (parseModule)
import Syntax.Macroexpand
import Syntax.Intermediate
import Syntax.Conversions
import Typecheck.Typecheck(runChecker)
import qualified Typecheck.Context as Ctx
import qualified Typecheck.InfContext as InfCtx
import Interpret.EvalM (local, throwError)
import Interpret.Transform (lift)
import Interpret.Modules.Core
import qualified Core

import qualified Data.Map as Map


moduleContext = Environment {
  localCtx = Map.empty,
  currentModule = Module coreModule,
  globalModule = Module Map.empty}

  
buildModule :: Map.Map String Expr -> String -> EvalM Expr
buildModule mp s = 
  case parseModule "internal-module" (pack s) of 
    Left err -> throwError (show err)
    Right ast -> do
      expanded <- local moduleContext (macroExpand ast)
      case toIntermediate expanded moduleContext of 
        Left err -> do 
          throwError err
        Right val -> do
          result <- toTIntermediate val (Ctx.envToCtx moduleContext)
          (checked, _) <- case runChecker result (InfCtx.envToCtx moduleContext) of 
            Left err -> throwError err
            Right val -> pure val
          core <- case runExcept (Core.toCore checked) of 
            Left err -> throwError err
            Right val -> pure val
          local moduleContext (Core.eval core)
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

  
