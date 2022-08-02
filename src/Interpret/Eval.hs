module Interpret.Eval (Expr,
                       EvalM,
                       evalToIO,

                       liftFun,
                       liftFun2,
                       liftFun3,
                       liftFun4) where

import Prelude hiding (lookup)

import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Control.Lens as Lens -- ((+=), use)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import qualified Interpret.Transform as Action
import Typecheck.TypeUtils(isLarge)

import Interpret.EvalM
  
import Data
import qualified Data.Map as Map
import Interpret.Transform hiding (lift)




evalToIO :: EvalM a -> Environment -> ProgState -> IO (Maybe (a, ProgState))
evalToIO (ActionMonadT inner_mnd) ctx state =
  case runState (runExceptT (runReaderT inner_mnd ctx)) state of
    (Right (Value obj), state') -> do
      return $ Just (obj, state')
    (Right (RaiseAction cnt id1 id2 args (Just f)), state') -> do
      result <- f args
      accumEffects result cnt state'
    (Right (RaiseAction cnt id1 id2 args Nothing), state') -> do
      putStrLn $ "Action Called Without Being Handled: ("  ++ show id2 ++ "," ++ show id2 ++ ")"
      return Nothing
    (Left err, state') -> do
      putStrLn $ "error: " ++ err
      return Nothing
  where
    accumEffects :: EvalM Expr -> (Expr -> EvalM a) -> ProgState -> IO (Maybe (a, ProgState))
    accumEffects (ActionMonadT inner_mnd) cnt state = 
      case runState (runExceptT (runReaderT inner_mnd ctx)) state of
        (Right (RaiseAction cnt2 id1 id2 args (Just f)), state') -> do 
          result <- f args
          accumEffects result (\x -> cnt2 x >>= cnt) state'
        (Right (Value obj), state') -> do
          evalToIO (cnt obj) ctx state'
        (Right (RaiseAction _ id1 id2 _ Nothing), state') -> do
          putStrLn $ "Action Called Without Default" ++ show (id1, id2)
          return Nothing
        (Left err, state') -> do
          putStrLn $ "error: " ++ err
          return Nothing


liftFun :: (Expr -> EvalM Expr) -> ModulusType -> Expr
liftFun f ty = InbuiltFun f ty

liftFun2 :: (Expr -> Expr -> EvalM Expr) -> ModulusType -> Expr
liftFun2 f ty = InbuiltFun (\x -> pure $ liftFun (f x) (getRetTy ty)) ty 

liftFun3 :: (Expr -> Expr -> Expr -> EvalM Expr) -> ModulusType -> Expr 
liftFun3 f ty = InbuiltFun (\x -> pure $ liftFun2 (f x) (getRetTy ty)) ty 

liftFun4 :: (Expr -> Expr -> Expr -> Expr -> EvalM Expr) -> ModulusType -> Expr 
liftFun4 f ty = InbuiltFun (\x -> pure $ liftFun3 (f x) (getRetTy ty)) ty 

getRetTy :: ModulusType -> ModulusType
getRetTy (MArr _ t) = t
getRetTy (MDep _ _ t) = t
getRetTy (ImplMDep _ _ t) = t
