{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Interpret.EvalM where

import qualified Control.Applicative

import Control.Monad.State (MonadState, runState)
import Control.Monad.Except (MonadError, runExceptT)
import Control.Monad.Reader (MonadReader, runReaderT)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State

import Data(EvalT(..), Neutral(..), Normal(..))
import Control.Lens (use, (+=))
import Data(Eval, EvalT, Environment, ProgState, uid_counter, var_counter)

type Environment' = Environment Eval
type ProgState' = ProgState Eval

instance Functor m => Functor (EvalT m) where 
  fmap f = EvalT . fmap f . unEvalT  

-- TODO: haskell complains if we put an applicative here :(
instance Monad m => Applicative (EvalT m) where 
  pure = EvalT . Control.Applicative.pure
  f <*> v = EvalT $ (unEvalT f <*> unEvalT v)

instance Monad m => Monad (EvalT m) where 
  return = EvalT . return

  m >>= f = EvalT $ unEvalT m >>= (unEvalT . f)
  

instance Monad m => MonadReader (Environment (EvalT m)) (EvalT m) where 
  ask = EvalT Reader.ask

  local f m = EvalT $ Reader.local f (unEvalT m)

instance Monad m => MonadState (ProgState (EvalT m)) (EvalT m) where 
  get = EvalT $ Reader.lift $ Except.lift $ State.get

  put v = EvalT $  Reader.lift $ Except.lift $ State.put v
  
instance Monad m => MonadError String (EvalT m) where 
  throwError err = EvalT $ Reader.lift $ Except.throwError err

  catchError mnd fnc = EvalT $ (unEvalT mnd) `Except.catchError` (unEvalT . fnc) 


  
freshID :: MonadState (ProgState m) m => m Int
freshID = do
  id <- use uid_counter
  uid_counter += 1
  pure id

freshIVar :: MonadState (ProgState m) m => m Int
freshIVar = do
  id <- use var_counter 
  var_counter += 1
  pure id

freshVar :: MonadState (ProgState m) m => m (Normal m)
freshVar = do
  id <- use var_counter 
  var_counter += 1
  pure (Neu (NeuVar ("#" <> show id) (NormUniv 0)) (NormUniv 0))


--runEvalT :: EvalT m a -> Environment (EvalT m) -> ProgState (EvalT m) -> (a, ProgState (EvalT m))


runEval :: Eval a -> Environment Eval -> ProgState Eval -> Either String (a, ProgState Eval)  
runEval mnd env state =
  case runState (runExceptT (runReaderT (unEvalT mnd) env)) state of
    (Right obj, state') -> Right (obj, state')
    (Left err, state') -> Left ("err: " <> err)
