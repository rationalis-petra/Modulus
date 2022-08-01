module Syntax.Macroexpand where

import Data(Value(..),
            -- Intermediate(..),
            AST (..),
            ModulusType(Undef),
            Context,
            EvalM,
            Core(CVal, CApp),
            ProgState) 

import Interpret.Transform (lift)
import qualified Interpret.Context as Ctx
-- import Interpret.Eval(Expr, evalToIO, eval) 
import Interpret.EvalM(ask, throwError) 

import qualified Core

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
  ctx <- ask
  case ast of
    (Cons (x : xs)) -> case x of
      (Atom (Symbol s)) -> 
        case Ctx.lookup s ctx of 
          Just val -> case val of
            (InbuiltMac f) -> (,) <$> f xs <*> pure True
            (CMacro argnames bdy ctx ty) -> do
              applyMacro (CFunction argnames bdy ctx ty) xs
            _ -> do
              zipped <- mapM (\v -> macroEval v) (x : xs)
              let (xs', bs) = unzip zipped
              return (Cons xs', (foldr (||) False bs))
          Nothing -> do
            zipped <- mapM (\v -> macroEval v) (x : xs)
            let (xs', bs) = unzip zipped
            return (Cons xs', (foldr (||) False bs))
      (Atom (InbuiltMac f)) -> (,) <$> f xs <*> pure True
      (Atom (CMacro argnames bdy ctx ty)) -> do
        applyMacro (CFunction argnames bdy ctx ty) xs
      _ -> do
        zipped <- mapM (\v -> macroEval v) (x : xs)
        let (xs', bs) = unzip zipped
        return (Cons xs', (foldr (||) False bs))
    _ -> return (ast, False)

  where
    applyMacro ::  Value EvalM -> [AST] -> EvalM (AST, Bool)
    applyMacro macro xs =
          (,)
          <$> (toAST =<< Core.eval (unfold (CVal macro) (map AST xs)))
          <*> pure True

    unfold :: Core -> [(Value EvalM)] -> Core
    unfold v [] = v
    unfold v (x:xs) = unfold (CApp v (CVal x)) xs

    toAST :: Value EvalM -> EvalM AST
    toAST (AST a) = pure a
    toAST _ = throwError "expecting macro to return AST or List AST"
  

