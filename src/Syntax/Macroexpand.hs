module Syntax.Macroexpand where

import Data(-- Intermediate(..),
            Normal,
            Normal'(..),
            AST (..),
            EvalM,
            Core(CNorm, CApp),
            ProgState) 

import qualified Interpret.Eval as Eval
import Interpret.Transform (lift)
import qualified Interpret.Environment as Env
import Interpret.EvalM(ask, throwError) 

  -- TODO: change macro-expansion to incorporate splicing

macroExpand :: AST -> EvalM AST
macroExpand ast = do
  (ast', runAgain) <- macroEval ast 
  if runAgain then do
    ast'' <- macroExpand ast'
    return  ast''
  else
    return ast'

macroEval :: AST -> EvalM (AST, Bool)
macroEval ast = do
  env <- ask
  case ast of
    (Cons (x : xs)) -> case x of
      (Atom (Symbol s)) -> 
        case Env.lookupMaybe s env of 
          Just (val, _) -> case val of
            (BuiltinMac f) -> (,) <$> f xs <*> pure True
            -- (CMacro argnames bdy env ty) -> do
            --   applyMacro (CFunction argnames bdy env ty) xs
            _ -> do
              zipped <- mapM (\v -> macroEval v) (x : xs)
              let (xs', bs) = unzip zipped
              return (Cons xs', (foldr (||) False bs))
          Nothing -> do
            zipped <- mapM (\v -> macroEval v) (x : xs)
            let (xs', bs) = unzip zipped
            return (Cons xs', (foldr (||) False bs))
      (Atom (BuiltinMac f)) -> (,) <$> f xs <*> pure True
      -- (Atom (CMacro argnames bdy env ty)) -> do
      --   applyMacro (CFunction argnames bdy env ty) xs
      _ -> do
        zipped <- mapM (\v -> macroEval v) (x : xs)
        let (xs', bs) = unzip zipped
        return (Cons xs', (foldr (||) False bs))
    _ -> return (ast, False)

  where
    applyMacro :: Normal -> [AST] -> EvalM (AST, Bool)
    applyMacro macro xs =
          (,)
          <$> (toAST =<< Eval.eval (unfold (CNorm macro) (map AST xs)))
          <*> pure True

    unfold :: Core -> [Normal] -> Core
    unfold v [] = v
    unfold v (x:xs) = unfold (CApp v (CNorm x)) xs

    toAST :: Normal -> EvalM AST
    toAST (AST a) = pure a
    toAST _ = throwError "expecting macro to return AST or List AST"
  

