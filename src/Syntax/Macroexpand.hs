module Syntax.Macroexpand where

import Data(Object(..),
            Intermediate(..),
            AST (..),
            ModulusType(Undef),
            Context,
            EvalM,
            ProgState) 

import Interpret.Transform (lift)
import qualified Interpret.Context as Ctx
import Interpret.Eval(Expr, evalToIO, eval) 
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
  ctx <- ask
  case ast of
    (Cons (x : xs)) -> case x of
      (Atom (Symbol s)) -> 
        case Ctx.lookup s ctx of 
          Just val -> case val of
            (InbuiltMac f) -> (,) <$> f xs <*> pure True
            (Macro argnames bdy ctx) -> do
              applyMacro (Function argnames bdy ctx) xs
            _ -> do
              zipped <- mapM (\v -> macroEval v) (x : xs)
              let (xs', bs) = unzip zipped
              return (Cons xs', (foldr (||) False bs))
          Nothing -> do
            zipped <- mapM (\v -> macroEval v) (x : xs)
            let (xs', bs) = unzip zipped
            return (Cons xs', (foldr (||) False bs))
      (Atom (InbuiltMac f)) -> (,) <$> f xs <*> pure True
      (Atom (Macro argnames bdy ctx)) -> do
        applyMacro (Function argnames bdy ctx) xs
      _ -> do
        zipped <- mapM (\v -> macroEval v) (x : xs)
        let (xs', bs) = unzip zipped
        return (Cons xs', (foldr (||) False bs))
    _ -> return (ast, False)

  where
    applyMacro :: Expr -> [AST] -> EvalM (AST, Bool)
    applyMacro macro xs =
          (,)
          <$> (toAST =<< eval (unfold (IValue macro) (map AST xs)))
          <*> pure True

    unfold :: Intermediate -> [Expr] -> Intermediate
    unfold v [] = v
    unfold v (x:xs) = unfold (IApply v (IValue x)) xs

    toAST :: Expr -> EvalM AST
    toAST (AST a) = return a
    toAST _ = throwError "expecting macro to return AST or List AST"
  

