module Interpret.EvalM where

import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import qualified Interpret.Transform as Action

import qualified Control.Lens as Lens -- ((+=), use)
import Data(EvalM, ActionMonadT(..), Context, ProgState, uid_counter, var_counter)


ask :: EvalM Context
ask = Action.lift $ Reader.ask

local :: Context -> EvalM a -> EvalM a
local ctx m = localF (\_ -> ctx) m

localF :: (Context -> Context) -> EvalM a -> EvalM a
localF f (ActionMonadT mnd) =
  ActionMonadT (Reader.local f mnd)

throwError :: String -> EvalM a
throwError err = Action.lift $ Reader.lift $ Except.throwError err

use v = Action.lift $ Reader.lift $ Except.lift $ Lens.use v
a += b = Action.lift $ Reader.lift $ Except.lift $ a Lens.+= b

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
