{-# LANGUAGE TemplateHaskell #-}
module Core where
import Data

import Data.Text (Text, pack, unpack)
import Data.Vector (Vector)

import Control.Lens hiding (Context)
import Control.Monad.State (State) 
import Control.Monad.Except (ExceptT, Except) 
import Control.Monad.Reader (ReaderT) 

import qualified Data.Map as Map
import qualified Control.Monad.Except as Except 
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State

import Typecheck.TypeUtils
import Interpret.Transform
import Syntax.TIntermediate

import qualified Interpret.Environment as Env
import qualified Interpret.Type as Type
import qualified Interpret.Transform as Action


type SigDefn = (Map.Map String TypeNormal)


-- PValue = Program Value 
type PValue = Value EvalM

-- "correctly" lifted monadic operations for eval
ask = Action.lift $ Reader.ask
local :: Environment -> EvalM a -> EvalM a
local env m = localF (\_ -> env) m

localF :: (Environment -> Environment) -> EvalM a -> EvalM a
localF f (ActionMonadT mnd) =
  ActionMonadT (Reader.local f mnd)
throwError err = Action.lift $ Reader.lift $ Except.throwError err

evalTop :: TopCore -> EvalM (Either Expr (Environment -> Environment))
evalTop (TopExpr e) = eval e >>= (\val -> pure (Left val))
evalTop (TopDef def) = case def of
  SingleDef name body ty -> do
    val <- eval body
    pure (Right (Env.insertCurrent name val))
  OpenDef body sig -> do
    mdle <- eval body
    case mdle of 
      Module m ->
        pure (Right (\env ->
                       Map.foldrWithKey (\k _ env ->
                                           let Just val = Map.lookup k m in
                                             Env.insertCurrent k val env)
                       env sig))
      _ -> throwError "cannot open non-module"
  -- VariantDef name params id variants ty ->
  --   let addVarType :: Environment -> Environment
  --       addVarType = Env.insert name (varFn params)

  --       varFn :: [String] -> (Value EvalM)
  --       varFn [] = Type ty
  --       varFn (p:ps) = (CFunction p (CVal $ varFn ps) Env.empty (vartype (p : ps)))

  --       vartype [] = (NormUniv 0)
  --       vartype (x:xs) = MArr (NormUniv 0) (vartype xs)

  --       addAlternatives :: [(String, Int, [TypeNormal])] -> Environment -> Environment
  --       addAlternatives ((nme, vid, types) : vs) env =
  --         let ty = mktype params types
  --             env' = Env.insert nme (CConstructor nme id vid (length variants) params [] ty) env
  --         in addAlternatives vs env'
  --       addAlternatives [] env = env

  --       mktype :: [String] -> [TypeNormal] -> TypeNormal
  --       mktype (p:ps) ts = ImplMDep (NormUniv 0) p (mktype ps ts)
  --       mktype [] (t:ts) = MArr t (mktype [] ts)
  --       mktype [] [] = ty 
  --   in
  --     pure (Right (addVarType . addAlternatives variants))
  
-- TODO: can we write core as an GADT so as to avoid exceptions?
eval :: Core -> EvalM Expr
eval (CVal e) = pure e
eval (CSym s) = do 
  env <- ask 
  case Env.lookup s env of 
    Just val -> pure val
    Nothing -> throwError ("could not find symbol " <> s)
eval (CDot e field) = do 
  mdle <- eval e
  case mdle of 
    Module m -> case Map.lookup field m of
      Just x -> pure x
      Nothing -> throwError ("couldn't find field" <> field)
    Type norm -> Type <$> Type.eval (TyDot (TyNorm norm) field)
    _ -> throwError ("tried to get field" <> field <> "from non-module or struct")
eval (CIF cond e1 e2) = do
  b <- eval cond
  case b of 
    (PrimVal (Bool True)) -> eval e1
    (PrimVal (Bool False)) -> eval e2

eval (CApp e1 e2) = do
  -- TODO: how to handle dependent types??
  fnc <- eval e1
  case fnc of 
    InbuiltFun f _ -> do 
      arg <- eval e2
      f arg
    CFunction var body fn_env ty ->  do
      arg <- eval e2
      let new_env = case var of
            "_" -> fn_env
            _ -> Env.insert var arg fn_env
      local new_env (eval body)
    CConstructor name id1 id2 n (x:xs) vars ty -> do
      arg <- eval e2
      pure (CConstructor name id1 id2 n xs vars ty)
    CConstructor name id1 id2 0 [] l ty -> do
      throwError ("non-function called " <> show fnc)
    CConstructor name id1 id2 n [] l ty -> do
      arg <- eval e2
      pure (CConstructor name id1 id2 (n - 1) [] (arg : l) ty)
    n -> throwError ("non-function called " <> show n)
eval (CAbs var body ty) = do
  env <- ask
  pure $ CFunction var body env ty

eval (CSct body) = Module <$> evalDefs body
  where
    evalDefs [] = pure Map.empty
    evalDefs ((SingleDef nme body ty) : tl) = do
      val <- eval body
      mdle <- localF (Env.insert nme val) (evalDefs tl)
      pure (Map.insert nme val mdle)

    evalDefs ((OpenDef body sig) : tl) = do 
      mdle <- eval body
      mdleMap <- case mdle of 
        (Module m) -> pure m
        _ -> throwError "non-module used in open!"
      let newEnv env = Map.foldrWithKey (\k v env -> case Map.lookup k mdleMap of  
                                            Just x -> Env.insert k x env) env sig
      localF newEnv (evalDefs tl)

eval (CSig body) = (Type . NormSig) <$> evalDefs body
  where
    evalDefs :: [Definition] -> EvalM [(String, TypeNormal)]
    evalDefs [] = pure []
    evalDefs ((SingleDef nme body ty) : tl) = do
      val <- eval body
      ty <- case val of 
        (Type t) -> pure t
        _ -> throwError "signatures can only contain types!"
      mdle <- localF (Env.insert nme (Type ty)) (evalDefs tl)
  
      pure ((nme, ty) : mdle)

    evalDefs ((OpenDef body sig) : tl) = do 
      mdle <- eval body
      mdleMap <- case mdle of 
        (Module m) -> pure m
        _ -> throwError "non-module used in open!"
      let newEnv env = Map.foldrWithKey (\k v env -> case Map.lookup k mdleMap of  
                                            Just x -> Env.insert k x env) env sig
      localF newEnv (evalDefs tl)


  
err = Except.throwError

toTopCore :: TIntTop TypeNormal -> Except String TopCore  
toTopCore (TDefinition def) = TopDef <$> fromDef def
  where
    fromDef (TSingleDef name body (Just ty)) = do
      coreBody <- toCore body
      pure (SingleDef name coreBody (TyNorm ty))
    fromDef (TSingleDef name body Nothing) = err "definitions must be typed"

    fromDef (TOpenDef body (Just ty)) = do
      coreBody <- toCore body
      let (NormSig sig) = ty
      pure (OpenDef coreBody (Map.fromList (map (\(var, val) -> (var, TyNorm val)) sig)))
    fromDef (TOpenDef body Nothing) = err "definitions must be typed"

    -- fromDef (TVariantDef nme params id alts ty) = pure (VariantDef nme params id alts ty)
toTopCore (TExpr v) = TopExpr <$> toCore v


toCore :: TIntermediate TypeNormal -> Except String Core  
toCore (TType ty) = pure (CVal (Type ty))
toCore (TValue v) = pure (CVal v)
toCore (TSymbol s) = pure (CSym s)
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
    mkLambdaTyVal :: [(TArg TypeNormal, Bool)] -> TIntermediate TypeNormal -> TypeNormal -> Except String Core
    mkLambdaTyVal [] body _ = toCore body
    mkLambdaTyVal (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyVal args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyVal (arg : args) body (NormDep var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormDep var l r)
    mkLambdaTyVal (arg : args) body (NormImplDep var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormImplDep var l r)


    mkLambdaTyExpr :: [(TArg TypeNormal, Bool)] -> TIntermediate TypeNormal -> TypeNormal -> Except String Core
    mkLambdaTyExpr [] body _ = toCore body
    mkLambdaTyExpr (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyExpr (arg : args) body (NormDep var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormDep var l r)
    mkLambdaTyExpr (arg : args) body (NormImplDep var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormImplDep var l r)

    getVar :: (TArg ty, Bool) -> String
    getVar (BoundArg var _, _)  = var
    getVar (InfArg var _  , _)  = var

toCore (TModule map) = do
  coreDefs <- mapM defToCore map
  pure (CSct coreDefs)
  where
    defToCore (TSingleDef nme bdy (Just ty)) = do
      bdy' <- toCore bdy
      pure (SingleDef nme bdy' (TyNorm ty))
    defToCore (TSingleDef nme bdy Nothing) = err "definition not typed"
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        NormSig sm -> pure sm
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' (Map.map TyNorm (Map.fromList sig)))
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [TypeNormal])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [TypeNormal])]

  
  -- = SingleDef String Core TypeNormal
  -- | VariantDef String [String] [(String, [Core])] 
  -- | EffectDef  String [String] [(String, [Core])]
  -- | OpenDef Core SigDefn

  
  -- = TVariantDef String [String] Int [(String, Int, [TypeNormal])]
  -- | TEffectDef  String [String] Int [(String, Int, [TypeNormal])]
  -- | TSingleDef  String TIntermediate (Maybe TypeNormal)
  -- | TOpenDef TIntermediate (Maybe TypeNormal)

  
toCore (TSignature map) = do
  coreDefs <- mapM defToCore map
  pure (CSig coreDefs)
  where
    defToCore (TSingleDef nme bdy t) = do
      bdy' <- toCore bdy
      -- TODO: this is bad, make sure to properly check signatures for well-formedness
      --  or, is this done during typechecking??
      -- TypeN is the type of signatures??
      pure (SingleDef nme bdy' (TyNorm (NormUniv 0)))
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        NormSig sm -> pure sm
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' (Map.map TyNorm (Map.fromList sig)))
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [TypeNormal])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [TypeNormal])]

toCore (TIF cond e1 e2) = do
  cond' <- toCore cond
  e1' <- toCore e1
  e2' <- toCore e2
  pure (CIF cond' e1' e2')

-- toCore x = err ("unimplemented" <> show x)
