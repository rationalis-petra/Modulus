module Syntax.Conversions where

import Data(Intermediate(..),
            Expr,
            Value(Type, Function, CConstructor),
            IDefinition(..),
            IPattern(..),
            EvalM,
            Core (CVal),
            Definition(..),
            Arg(..),
            ModulusType(..))

import Interpret.EvalM (local, fresh_id, fresh_var, throwError)
import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT, runExcept)
import Interpret.Transform
import qualified Interpret.Environment as Env
import qualified Typecheck.Context as Ctx 
import Syntax.TIntermediate
import Typecheck.TypeUtils (isLarge)

import qualified Core
import qualified Typecheck.Typecheck

-- evaluate for the typechecker
-- typeEval :: Intermediate -> CheckEnv -> EvalM Expr
-- typeEval ctx = 
  
type MT = ModulusType

  

toTIntermediateTop :: Intermediate -> Ctx.Context -> EvalM (TIntTop MT)
toTIntermediateTop (IDefinition def) ctx =    
  case def of 
    ISingleDef s i -> do
      t <- toTIntermediate i ctx
      pure (TDefinition $ TSingleDef s t Nothing)
    IOpenDef i -> do
      t <- toTIntermediate i ctx
      pure (TDefinition $ TOpenDef t Nothing)
    IVariantDef nme params alternatives -> do
      id <- fresh_id
      let
        -- TODO: how to add the variants in recursively...??
        -- Idea: perform a recursive substitution, hmm?
        -- Idea: use Haskell's laziness??
        varVal = Function params (IValue $ Type $ MNamed id nme (map MVar params) []) Env.empty
        varType = mkTFun params
      
        mkTFun (p : ps) = MArr (TypeN 1) (mkTFun ps)
        mkTFun [] = TypeN 1
      
        newCtx :: Ctx.Context
        newCtx = foldr (\s ctx -> Ctx.insertVal s (Type $ MVar s) (TypeN 1) ctx) ctx params  
        newCtx' = Ctx.insertVal nme varVal varType newCtx
         
      alts <- local (Ctx.ctxToEnv newCtx') (evalAlts 0 alternatives)
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
          ty <- evalIntermediate i ctx
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
toTIntermediate :: Intermediate -> Ctx.Context -> EvalM (TIntermediate MT)
toTIntermediate (IValue expr) _ = pure (TValue expr)
toTIntermediate (ISymbol s) env = pure (TSymbol s)
toTIntermediate (IAccess i s) env = do
  t <- toTIntermediate i env
  pure (TAccess t s)


-- Note: implicit argument resolution done during type-checking!
toTIntermediate (IApply i1 i2) ctx = do
  i1' <- toTIntermediate i1 ctx
  i2' <- toTIntermediate i2 ctx
  pure (TApply i1' i2')

toTIntermediate (ILambda args bdy) ctx = do
  (args', ctx') <- processArgs args ctx
  bdy' <- toTIntermediate bdy ctx'
  pure $ TLambda args' bdy' Nothing
  where
    processArgs :: [(Arg, Bool)] -> Ctx.Context -> EvalM ([(TArg MT, Bool)], Ctx.Context)
    processArgs [] ctx = pure ([], ctx)
    processArgs ((Sym s, b) : xs) ctx =
      if b then  do
        (tl, ctx') <- processArgs xs (Ctx.insertVal s (Type $ MVar s) (TypeN 1) ctx)
        pure $ ((BoundArg s (TypeN 1), b) : tl, ctx')
      else do
        (tl, ctx') <- processArgs xs ctx
        var <- fresh_var
        pure $ (((InfArg s var), b) : tl, ctx')
    processArgs ((Annotation s i, b) : xs) ctx = do
      ty <- local (Ctx.ctxToEnv ctx) (evalIntermediate i ctx)
      case ty of
        Type t ->
          if isLarge t then do
            (tl, ctx') <- processArgs xs (Ctx.insertVal s (Type $ MVar s) (TypeN 1) ctx)
            pure (((BoundArg s t, b): tl), ctx')
          else do
            (tl, ctx') <- processArgs xs ctx
            pure (((ValArg s t, b) : tl), ctx')
        _ -> throwError ("expected type in function annotation, got: " <> show ty)


toTIntermediate (IModule defList) env = do
  TModule <$> getDefs defList env
  where
    getDefs :: [IDefinition] -> Ctx.Context -> EvalM [TDefinition MT]
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
    getDefs :: [IDefinition] -> Ctx.Context -> EvalM [TDefinition MT]
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

toTIntermediate (IMatch e1 cases) ctx = do 
  e1' <- toTIntermediate e1 ctx
  cases' <- mapM toCase cases 
  pure (TMatch e1' cases')

  where
    toCase :: (IPattern, Intermediate) -> EvalM (TPattern MT, TIntermediate MT)
    toCase (ipat, e) = do 
      tpat <- toTPat ipat 
      e' <- toTIntermediate e ctx
      pure (tpat, e')

    toTPat :: IPattern -> EvalM (TPattern MT)
    toTPat IWildCard = pure TWildCardPat
    toTPat (ISingPattern s) = pure (TBindPat s)
    toTPat (ICheckPattern pat subPatterns) = do
      subPatterns' <- mapM toTPat subPatterns
      extractPattern pat subPatterns'

    extractPattern expr subPatterns = do
      val <- local (Ctx.ctxToEnv ctx) (evalIntermediate expr ctx)
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



evalIntermediate :: Intermediate -> Ctx.Context -> EvalM (Value EvalM)
evalIntermediate term ctx = do
  t_term <- toTIntermediate term ctx
  c_term <- case runExcept (Core.toCore t_term) of 
        Left err -> throwError err
        Right val -> pure val
  Core.eval c_term
