module Syntax.Conversions where

import Data(Intermediate(..),
            Expr,
            Object(Type, Function, CConstructor),
            IDefinition(..),
            IPattern(..),
            EvalM,
            Core (CVal),
            Definition(..),
            Arg(..),
            ModulusType(..))

import Data.Environments
import Interpret.Eval (eval)
import Interpret.EvalM (local, fresh_id, fresh_var, throwError)
import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Interpret.Transform
import qualified Interpret.Context as Ctx
import qualified Typecheck.EnvironmentOld as Env 
import Syntax.TIntermediate
import Typecheck.TypeUtils (isLarge)

import qualified Core
import qualified Typecheck.Typecheck

-- evaluate for the typechecker
-- typeEval :: Intermediate -> CheckEnv -> EvalM Expr
-- typeEval ctx = 
  
type MT = ModulusType

  

toTIntermediateTop :: Intermediate -> CheckEnv -> EvalM (TIntTop MT)
toTIntermediateTop (IDefinition def) env =    
  case def of 
    ISingleDef s i -> do
      t <- toTIntermediate i env
      pure (TDefinition $ TSingleDef s t Nothing)
    IOpenDef i -> do
      t <- toTIntermediate i env
      pure (TDefinition $ TOpenDef t Nothing)
    IVariantDef nme params alternatives -> do
      id <- fresh_id
      let
        -- TODO: how to add the variants in recursively...??
        -- Idea: perform a recursive substitution, hmm?
        varType = Val (Function params (IValue $ Type $ MNamed id nme (map MVar params) []) Ctx.empty)
                      (mkTFun params)
      
        mkTFun (p : ps) = MArr (TypeN 1) (mkTFun ps)
        mkTFun [] = TypeN 1
      
        newEnv = foldr (\s env -> Env.insert s (Val (Type $ MVar s) (TypeN 1)) env) env params  
        newEnv' = Env.insert nme varType newEnv
         
      alts <- local (Env.toCtx newEnv') (evalAlts 0 alternatives)
      let (alts', varType') = recursiveSubst id nme (map MVar params) alts
      pure (TDefinition $ TVariantDef nme params id alts' varType')
      where
        evalAlts _ [] = pure []
        evalAlts n ((s, ilist) : tl) = do
          types <- evalTypes ilist
          tl' <- evalAlts (n + 1) tl
          pure ((s, n, types) : tl')

        evalTypes [] = pure []
        evalTypes (i:is) = do
          ty <- eval i 
          case ty of 
            (Type t) -> do
              ts <- evalTypes is
              pure (t : ts)
            _ -> throwError "variant requires types"
  
        recursiveSubst :: Int -> String -> [ModulusType] -> [(String, Int, [ModulusType])]
                       -> ([(String, Int, [ModulusType])], ModulusType)
        recursiveSubst id nme params alts = 
          let alts' = map (\(s, n, ts) -> (s, n, map subst ts)) alts
              varType' = MNamed id nme params (map (\(_, _, t) -> t) alts')

              -- TODO: finish this function!
              subst (MNamed id' n p a) = if id == id' then
                varType' else (MNamed id' n p a)
              subst (MArr t1 t2) = MArr (subst t1) (subst t2) 
              subst (MPrim p) = (MPrim p)
              subst (MVar v) = (MVar v)
              subst (TypeN n) = (TypeN n)
          in (alts', varType')
      

  
toTIntermediateTop i env = TExpr <$> toTIntermediate i env

-- TODO: make sure to update the context with typeLookup
toTIntermediate :: Intermediate -> CheckEnv -> EvalM (TIntermediate MT)
toTIntermediate (IValue expr) _ = pure (TValue expr)
toTIntermediate (ISymbol s) env = pure (TSymbol s)
toTIntermediate (IAccess i s) env = do
  t <- toTIntermediate i env
  pure (TAccess t s)


-- Note: implicit argument resolution done during type-checking!
toTIntermediate (IApply i1 i2) env = do
  i1' <- toTIntermediate i1 env
  i2' <- toTIntermediate i2 env
  pure (TApply i1' i2')

toTIntermediate (ILambda args bdy) env = do
  (args', env') <- processArgs args env
  id <- fresh_var
  bdy' <- toTIntermediate bdy env'
  pure $ TLambda args' bdy' Nothing
  where
    processArgs :: [(Arg, Bool)] -> CheckEnv -> EvalM ([(TArg MT, Bool)], CheckEnv)
    processArgs [] env = pure ([], env)
    processArgs ((Sym s, b) : xs) env =
      if b then  do
        (tl, env') <- processArgs xs (Env.insert s (Val (Type $ MVar s) (TypeN 1)) env)
        pure $ ((BoundArg s (TypeN 1), b) : tl, env')
      else do
        (tl, env') <- processArgs xs env
        var <- fresh_var
        pure $ (((InfArg s var), b) : tl, env')
    processArgs ((Annotation s i, b) : xs) env = do
      ty <- local (Env.toCtx env) (eval i)
      case ty of
        Type t ->
          if isLarge t then do
            (tl, env') <- processArgs xs (Env.insert s (Val (Type $ MVar s) (TypeN 1)) env)
            pure (((BoundArg s t, b): tl), env')
          else do
            (tl, env') <- processArgs xs env
            pure (((ValArg s t, b) : tl), env')
        _ -> throwError ("expected type in function annotation, got: " <> show ty)


toTIntermediate (IModule defList) env = do
  TModule <$> getDefs defList env
  where
    getDefs :: [IDefinition] -> CheckEnv -> EvalM [TDefinition MT]
    getDefs [] _ = pure []
    getDefs (x:xs) env = case x of
      ISingleDef s i -> do
        hd <- toTIntermediate i env
        tl <- getDefs xs env 
        pure $ TSingleDef s hd Nothing : tl
      -- TODO: types of variants
      IVariantDef nme args variants -> -- String[String][(String,[Intermediate])]
        throwError "variants not implemented yet..."
      IEffectDef nme args effects -> -- String [String] [(String, [Intermediate])]
        throwError "effects not implemented yet..."
      IOpenDef i -> do
        opn <- TOpenDef <$> (toTIntermediate i env) <*> pure Nothing
        rest <- getDefs xs env
        pure $ opn : rest

toTIntermediate (ISignature defList) env = do
  TSignature <$> getDefs defList env
  where
    getDefs :: [IDefinition] -> CheckEnv -> EvalM [TDefinition MT]
    getDefs [] _ = pure []
    getDefs (x:xs) env = case x of
      ISingleDef s i -> do
        hd <- toTIntermediate i env
        tl <- getDefs xs env 
        pure $ TSingleDef s hd Nothing : tl
      -- TODO: types of variants
      IVariantDef nme args variants -> -- String[String][(String,[Intermediate])]
        throwError "variants in signatures not implemented yet..."
      IEffectDef nme args effects -> -- String [String] [(String, [Intermediate])]
        throwError "effects in signatures not implemented yet..."
      IOpenDef i -> do
        opn <- TOpenDef <$> (toTIntermediate i env) <*> pure Nothing
        rest <- getDefs xs env
        pure $ opn : rest
  
toTIntermediate (IIF cond e1 e2) env = do
  cond' <- toTIntermediate cond env
  e1' <- toTIntermediate e1 env
  e2' <- toTIntermediate e2 env
  pure (TIF cond' e1' e2')

toTIntermediate (IMatch e1 cases) env = do 
  e1' <- toTIntermediate e1 env
  cases' <- mapM toCase cases 
  pure (TMatch e1' cases')

  where
    toCase :: (IPattern, Intermediate) -> EvalM (TPattern MT, TIntermediate MT)
    toCase (ipat, e) = do 
      tpat <- toTPat ipat 
      e' <- toTIntermediate e env
      pure (tpat, e')

    toTPat :: IPattern -> EvalM (TPattern MT)
    toTPat IWildCard = pure TWildCardPat
    toTPat (ISingPattern s) = pure (TBindPat s)
    toTPat (ICheckPattern pat subPatterns) = do
      subPatterns' <- mapM toTPat subPatterns
      extractPattern pat subPatterns'

    extractPattern expr subPatterns = do
      val <- local (Env.toCtx env) (eval expr)
      case val of 
        -- TODO: what to do with params?
        CConstructor name id1 id2 len params [] ty ->
          if len == length subPatterns then
            pure (TVarPat id1 id2 subPatterns ty)
          else
            throwError ("subpatterns bad size for pattern: " <> name
                        <> " expected " <> show len <> "got" <> show (length subPatterns))
        _ -> throwError ("couldn't extract pattern from val: " <> show val)



toTIntermediate x _ = throwError ("toTIntermediate not implemented for: "  <> show x)
