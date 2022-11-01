module Interpret.EvalM where

import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State

import qualified Control.Lens as Lens -- ((+=), use)
import Data(EvalM, Environment, ProgState, uid_counter, var_counter)

ask :: EvalM Environment
ask = Reader.ask

localF :: (Environment -> Environment) -> EvalM a -> EvalM a
localF = Reader.local

local :: Environment -> EvalM a -> EvalM a
local env m = localF (\_ -> env) m

throwError :: String -> EvalM a
throwError err = Reader.lift $ Except.throwError err

use v = Reader.lift $ Except.lift $ Lens.use v
a += b = Reader.lift $ Except.lift $ a Lens.+= b

fresh_id :: EvalM Int
fresh_id = do
  id <- use uid_counter
  uid_counter += 1
  pure id

fresh_var :: EvalM Int
fresh_var = do
  id <- use var_counter
  var_counter += 1
  pure id

liftExcept :: Except.Except String a -> EvalM a
liftExcept e = case Except.runExcept e of 
  Right val -> pure val
  Left err -> throwError err

 
