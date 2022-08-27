module Syntax.Conversions where

import Data(EvalM,
            TopCore(..),
            Core (..),
            Definition(..),
            Normal,
            Normal'(..),
            Neutral,
            Neutral'(..))
import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           IPattern(..),
                           IArg(..))

import Interpret.EvalM (local, fresh_id, fresh_var, throwError)
import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, Except, runExceptT, runExcept)
import qualified Control.Monad.Except as Except 

import qualified Interpret.Environment as Env
import qualified Typecheck.Context as Ctx 
import Typecheck.Typecheck (typeCheck) 
import Syntax.TIntermediate
import qualified Interpret.Eval as Eval
import qualified Typecheck.Typecheck

  

toTIntermediateTop :: Intermediate -> Ctx.Context -> EvalM (TIntTop Core)
toTIntermediateTop (IDefinition def) ctx =    
  case def of 
    ISingleDef s i -> do
      t <- toTIntermediate i ctx
      pure (TDefinition $ TSingleDef s t Nothing)
    IOpenDef i -> do
      t <- toTIntermediate i ctx
      pure (TDefinition $ TOpenDef t Nothing)
    -- IVariantDef nme params alternatives -> do
    --   id <- fresh_id
    --   let
    --     -- varVal: the variant type itself, defined as a type-constructor
    --     -- (i.e. a function from a type to a type)
    --     varVal = mkVFun params 
    --     -- CFunction params (CVal $ Type $ MNamed id nme (map MVar params) []) Env.empty
    --     mkVFun [] = Type $ MNamed id nme (map MVar params) []
    --     mkVFun (p:ps) = CFunction p (mkBdy ps) Env.empty (mkTFun (p:ps))
    --       where
    --         mkBdy [] = CVal $ Type $ MNamed id nme (map MVar params) []
    --         mkBdy (p:ps) = CAbs p (mkBdy ps) (mkTFun (p:ps))

    --     -- varType: the type of the variant type constructor (i.e. type -> type -> ...)
    --     varType = mkTFun params
    --     mkTFun (p : ps) = MArr (TypeN 1) (mkTFun ps)
    --     mkTFun [] = TypeN 1
      
    --     newCtx :: Ctx.Context
    --     newCtx = foldr (\s ctx -> Ctx.insertVal s (Type $ MVar s) (TypeN 1) ctx) ctx params  
    --     newCtx' = Ctx.insertVal nme varVal varType newCtx
         
    --   alts <- local (Ctx.ctxToEnv newCtx') (evalAlts 0 alternatives)
    --   let (alts', varType') = recursiveSubst id nme (map MVar params) alts
    --   pure (TDefinition $ TVariantDef nme params id alts' varType')
    --   where
    --     evalAlts _ [] = pure []
    --     evalAlts n ((s, ilist) : tl) = do
    --       types <- evalTypes ilist
    --       tl' <- evalAlts (n + 1) tl
    --       pure ((s, n, types) : tl')

    --     evalTypes [] = pure []
    --     evalTypes (i:is) = do
    --       ty <- evalIntermediate i ctx
    --       case ty of 
    --         (Type t) -> do
    --           ts <- evalTypes is
    --           pure (t : ts)
    --         _ -> throwError "variant requires types"
  
    --     recursiveSubst :: Int -> String -> [TypeNormal] -> [(String, Int, [TypeNormal])]
    --                    -> ([(String, Int, [TypeNormal])], TypeNormal)
    --     recursiveSubst id nme params alts = 
    --       let alts' = map (\(s, n, ts) -> (s, n, map subst ts)) alts
    --           varType' = MNamed id nme params (map (\(_, _, t) -> t) alts')

    --           -- TODO: finish this function!
    --           -- subst (MNamed id' n p a) = if id == id' then
    --           --   varType' else (MNamed id' n p a)
    --           subst (NormArr t1 t2) = NormArr (subst t1) (subst t2) 
    --           subst (MPrim p) = (MPrim p)
    --           subst (MVar v) = (MVar v)
    --           subst (TypeN n) = (TypeN n)
    --       in (alts', varType')
      

  
toTIntermediateTop i env = TExpr <$> toTIntermediate i env

-- TODO: make sure to update the context with typeLookup
toTIntermediate :: Intermediate -> Ctx.Context -> EvalM (TIntermediate Core)
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

toTIntermediate (IImplApply i1 i2) ctx = do
  i1' <- toTIntermediate i1 ctx
  i2' <- toTIntermediate i2 ctx
  pure (TImplApply i1' i2')

toTIntermediate (ILambda args bdy) ctx = do
  (args', ctx') <- processArgs args ctx
  bdy' <- toTIntermediate bdy ctx'
  pure $ TLambda args' bdy' Nothing
  where
    processArgs :: [(IArg, Bool)] -> Ctx.Context -> EvalM ([(TArg Core, Bool)], Ctx.Context)
    processArgs [] ctx = pure ([], ctx)
    processArgs ((Sym s, b) : xs) ctx =
      if b then  do
        (tl, ctx') <- processArgs xs (Ctx.insertVal s (Neu (NeuVar s)) (NormUniv 0) ctx)
        pure (((BoundArg s (CNorm (NormUniv 0)), b) : tl), ctx')
      else do
        (tl, ctx') <- processArgs xs ctx
        var <- fresh_var
        pure $ (((InfArg s var), b) : tl, ctx')
    processArgs ((Annotation s i, b) : xs) ctx = do
      ty <- local (Ctx.ctxToEnv ctx) (evalIntermediate i ctx)
      case ty of
        -- TODO: check it it is a type (now an algorithmic judgement...)
        t -> do
          (tl, ctx') <- processArgs xs (Ctx.insertVal s (Neu $ NeuVar s) (NormUniv 0) ctx)
          pure (((BoundArg s (CNorm t), b) : tl), ctx')
        _ -> throwError ("expected type in function annotation, got: " <> show ty)


toTIntermediate (IModule defList) env = do
  TModule <$> getDefs defList env
  where
    getDefs :: [IDefinition] -> Ctx.Context -> EvalM [TDefinition Core]
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
    getDefs :: [IDefinition] -> Ctx.Context -> EvalM [TDefinition Core]
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
    toCase :: (IPattern, Intermediate) -> EvalM (TPattern Core, TIntermediate Core)
    toCase (ipat, e) = do 
      tpat <- toTPat ipat 
      e' <- toTIntermediate e ctx
      pure (tpat, e')

    toTPat :: IPattern -> EvalM (TPattern Core)
    toTPat IWildCard = pure TWildCardPat
    toTPat (ISingPattern s) = pure (TBindPat s)
    toTPat (ICheckPattern pat subPatterns) = do
      subPatterns' <- mapM toTPat subPatterns
      extractPattern pat subPatterns'

    extractPattern expr subPatterns = do
      val <- local (Ctx.ctxToEnv ctx) (evalIntermediate expr ctx)
      case val of 
        -- TODO: what to do with params?
        -- CConstructor name id1 id2 len params [] ty ->
        --   if len == length subPatterns then
        --     pure (TVarPat id1 id2 subPatterns (TyNorm ty))
        --   else
        --     throwError ("subpatterns bad size for pattern: " <> name
        --                 <> " expected " <> show len <> "got" <> show (length subPatterns))
        _ -> throwError ("couldn't extract pattern from val: " <> show val)



toTIntermediate x _ = throwError ("toTIntermediate not implemented for: "  <> show x)



evalIntermediate :: Intermediate -> Ctx.Context -> EvalM Normal
evalIntermediate term ctx = do
  t_term <- toTIntermediate term ctx
  (checked, _, _) <- typeCheck t_term ctx -- TODO: dodge??
  c_term <- case runExcept (toCore checked) of 
        Left err -> throwError err
        Right val -> pure val
  Eval.eval c_term



err = Except.throwError
  
toTopCore :: TIntTop Normal -> Except String TopCore  
toTopCore (TDefinition def) = TopDef <$> fromDef def
  where
    fromDef (TSingleDef name body (Just ty)) = do
      coreBody <- toCore body
      pure (SingleDef name coreBody ty)
    fromDef (TSingleDef name body Nothing) = err "definitions must be typed"

    fromDef (TOpenDef body (Just ty)) = do
      coreBody <- toCore body
      let (NormSig sig) = ty
      pure (OpenDef coreBody sig)
    fromDef (TOpenDef body Nothing) = err "definitions must be typed"

    -- fromDef (TVariantDef nme params id alts ty) = pure (VariantDef nme params id alts ty)
toTopCore (TExpr v) = TopExpr <$> toCore v


toCore :: TIntermediate Normal -> Except String Core  
toCore (TValue v) = pure (CNorm v)
toCore (TSymbol s) = pure (CVar s)
toCore (TAccess int field) = do
  body <- toCore int
  pure (CDot body field)
toCore (TApply t1 t2) = do
  c1 <- toCore t1
  c2 <- toCore t2
  pure $ CApp c1 c2
toCore (TImplApply t1 t2) = do
  c1 <- toCore t1
  c2 <- toCore t2
  pure $ CApp c1 c2
toCore (TLambda args body lty) = do
  ty <- case lty of 
    Just ty -> pure ty
    Nothing -> err "cannot convert untyped lambda to core!"
  mkLambdaTyVal args body ty

  where
    mkLambdaTyVal :: [(TArg Normal, Bool)] -> TIntermediate Normal -> Normal -> Except String Core
    mkLambdaTyVal [] body _ = toCore body
    mkLambdaTyVal (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyVal args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyVal (arg : args) body (NormProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormProd var l r)
    mkLambdaTyVal (arg : args) body (NormImplProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormImplProd var l r)


    mkLambdaTyExpr :: [(TArg Normal, Bool)] -> TIntermediate Normal -> Normal -> Except String Core
    mkLambdaTyExpr [] body _ = toCore body
    mkLambdaTyExpr (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyExpr (arg : args) body (NormProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormProd var l r)
    mkLambdaTyExpr (arg : args) body (NormImplProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormImplProd var l r)

    getVar :: (TArg ty, Bool) -> String
    getVar (BoundArg var _, _)  = var
    getVar (InfArg var _  , _)  = var

toCore (TModule map) = do
  coreDefs <- mapM defToCore map
  pure (CSct coreDefs)
  where
    defToCore (TSingleDef nme bdy (Just ty)) = do
      bdy' <- toCore bdy
      pure (SingleDef nme bdy' ty)
    defToCore (TSingleDef nme bdy Nothing) = err "definition not typed"
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        NormSig sm -> pure sm
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [Normal])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [Normal])]

  
  -- = SingleDef String Core Normal
  -- | VariantDef String [String] [(String, [Core])] 
  -- | EffectDef  String [String] [(String, [Core])]
  -- | OpenDef Core SigDefn

  
  -- = TVariantDef String [String] Int [(String, Int, [Normal])]
  -- | TEffectDef  String [String] Int [(String, Int, [Normal])]
  -- | TSingleDef  String TIntermediate (Maybe Normal)
  -- | TOpenDef TIntermediate (Maybe Normal)

  
toCore (TSignature map) = do
  coreDefs <- mapM defToCore map
  pure (CSig coreDefs)
  where
    defToCore (TSingleDef nme bdy t) = do
      bdy' <- toCore bdy
      -- TODO: this is bad, make sure to properly check signatures for well-formedness
      --  or, is this done during typechecking??
      -- TypeN is the type of signatures??
      pure (SingleDef nme bdy' (NormUniv 0))
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        NormSig sm -> pure sm
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [Normal])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [Normal])]

toCore (TIF cond e1 e2) = do
  cond' <- toCore cond
  e1' <- toCore e1
  e2' <- toCore e2
  pure (CIF cond' e1' e2')

toCore x = err ("unimplemented" <> show x)
