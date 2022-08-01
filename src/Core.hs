{-# LANGUAGE TemplateHaskell #-}
module Core where
import Data (Value (InbuiltFun, Module, Type, CFunction, PrimE, CConstructor,
                    CustomCtor),
             PrimE(Bool),
             TopCore(..),
             Expr,
             Definition(..),
             Core(..),
             ModulusType(..),
             ActionMonadT(ActionMonadT),
             ProgState,
             Context)

import Data.Text (Text, pack, unpack)
import Data.Vector (Vector)

import Control.Lens hiding (Context)
import Control.Monad.State (State) 
import Control.Monad.Except (ExceptT, Except) 
import Control.Monad.Reader (ReaderT) 
import qualified Control.Monad.Except as Except 
import qualified Control.Monad.Reader as Reader
import Typecheck.TypeUtils

import Interpret.Transform
import qualified Data.Map as Map
import Syntax.TIntermediate

import qualified Interpret.Context as Ctx
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import qualified Interpret.Transform as Action


type SigDefn = (Map.Map String ModulusType)



-- EvalM = Evaluation Monad
type EvalM = ActionMonadT (ReaderT Context (ExceptT String (State ProgState)))

-- PValue = Program Value 
type PValue = Value EvalM

-- "correctly" lifted monadic operations for eval
ask = Action.lift $ Reader.ask
local :: Context -> EvalM a -> EvalM a
local ctx m = localF (\_ -> ctx) m

localF :: (Context -> Context) -> EvalM a -> EvalM a
localF f (ActionMonadT mnd) =
  ActionMonadT (Reader.local f mnd)
throwError err = Action.lift $ Reader.lift $ Except.throwError err

evalTop :: TopCore -> EvalM (Either Expr (Context -> Context))
evalTop (TopExpr e) = eval e >>= (\val -> pure (Left val))
evalTop (TopDef def) = case def of
  SingleDef name body ty -> do
    val <- eval body
    pure (Right (Ctx.insertCurrent name val))
  OpenDef body sig -> do
    mdle <- eval body
    case mdle of 
      Module m ->
        pure (Right (\ctx ->
                       Map.foldrWithKey (\k _ ctx ->
                                           let Just val = Map.lookup k m in
                                             Ctx.insertCurrent k val ctx)
                       ctx sig))
      _ -> throwError "cannot open non-module"
  VariantDef name params id variants ty ->
    let addVarType :: Context -> Context
        addVarType = Ctx.insert name (varFn params)

        varFn [] = Type ty
        varFn (p:ps) = (CFunction p (CVal $ varFn ps) Ctx.empty (vartype (p : ps)))

        vartype [] = (TypeN 1)
        vartype (x:xs) = MArr (TypeN 1) (vartype xs)

        addAlternatives :: [(String, Int, [ModulusType])] -> Context -> Context
        addAlternatives ((nme, vid, types) : vs) ctx =
          let ty = mktype params types
              ctx' = Ctx.insert nme (CConstructor nme id vid (length variants) params [] ty) ctx
          in addAlternatives vs ctx'
        addAlternatives [] ctx = ctx

        mktype :: [String] -> [ModulusType] -> ModulusType
        mktype (p:ps) ts = ImplMDep (TypeN 1) p (mktype ps ts)
        mktype [] (t:ts) = MArr t (mktype [] ts)
        mktype [] [] = ty 
    in
      pure (Right (addVarType . addAlternatives variants))
  
-- TODO: can we write core as an GADT so as to avoid exceptions?
eval :: Core -> EvalM Expr
eval (CVal (Type t)) = Type <$> evalType t
eval (CVal e) = pure e
eval (CSym s) = do 
  ctx <- ask 
  case Ctx.lookup s ctx of 
    Just val -> pure val
    Nothing -> throwError ("could not find symbol " <> s)
eval (CDot e field) = do 
  mdle <- eval e
  case mdle of 
    Module m -> case Map.lookup field m of
      Just x -> pure x
      Nothing -> throwError ("couldn't find field" <> field)
    Type t -> pure (Type (MDot t field))
    _ -> throwError ("tried to get field" <> field <> "from non-module or struct")
eval (CIF cond e1 e2) = do
  b <- eval cond
  case b of 
    (PrimE (Bool True)) -> eval e2
    (PrimE (Bool False)) -> eval e2

eval (CApp e1 e2) = do
  -- TODO: how to handle dependent types??
  fnc <- eval e1
  case fnc of 
    InbuiltFun f _ -> do 
      arg <- eval e2
      f arg
    CFunction var body fn_ctx ty ->  do
      arg <- eval e2
      let new_ctx = case var of
            "_" -> fn_ctx
            _ -> Ctx.insert var arg fn_ctx
      local new_ctx (eval body)
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
  ctx <- ask
  pure $ CFunction var body ctx ty

eval (CMod body) = Module <$> evalDefs body
  where
    evalDefs [] = pure Map.empty
    evalDefs ((SingleDef nme body ty) : tl) = do
      val <- eval body
      mdle <- localF (Ctx.insert nme val) (evalDefs tl)
      pure (Map.insert nme val mdle)

    evalDefs ((OpenDef body sig) : tl) = do 
      mdle <- eval body
      mdleMap <- case mdle of 
        (Module m) -> pure m
        _ -> throwError "non-module used in open!"
      let newCtx ctx = Map.foldrWithKey (\k v ctx -> case Map.lookup k mdleMap of  
                                            Just x -> Ctx.insert k x ctx) ctx sig
      localF newCtx (evalDefs tl)

eval (CSig body) = (Type . Signature) <$> evalDefs body
  where
    evalDefs [] = pure Map.empty
    evalDefs ((SingleDef nme body ty) : tl) = do
      val <- eval body
      ty <- case val of 
        (Type t) -> pure t
        _ -> throwError "signatures can only contain types!"
      let var = largeToVar nme ty
      mdle <- localF (Ctx.insert nme var) (evalDefs tl)
  
      pure (Map.insert nme ty mdle)

    evalDefs ((OpenDef body sig) : tl) = do 
      mdle <- eval body
      mdleMap <- case mdle of 
        (Module m) -> pure m
        _ -> throwError "non-module used in open!"
      let newCtx ctx = Map.foldrWithKey (\k v ctx -> case Map.lookup k mdleMap of  
                                            Just x -> Ctx.insert k x ctx) ctx sig
      localF newCtx (evalDefs tl)

    largeToVar s t = if isLarge t then Type (MVar s) else (Type t)

evalType :: ModulusType -> EvalM ModulusType
evalType (MPrim p) = pure (MPrim p)
evalType (TypeN n) = pure (TypeN n)
evalType (MVar s) = do 
  env <- ask
  case Ctx.lookup s env of 
    Just v -> case v of 
      (Type t) -> pure t
      _ -> throwError "type variable contains non-type value!"
evalType (MArr t1 t2) = do
  t1' <- evalType t1
  t2' <- evalType t2
  pure (MArr t1' t2')
evalType (MDep t1 s t2) = do
  t1' <- evalType t1
  ctx <- ask
  t2' <- localF (Ctx.insert s (Type (MVar s))) (evalType t2) 
  pure (MDep t1' s t2')
evalType (ImplMDep t1 s t2) = do
  t1' <- evalType t1
  ctx <- ask
  t2' <- localF (Ctx.insert s (Type (MVar s))) (evalType t2) 
  pure (ImplMDep t1' s t2')
evalType (MNamed id nme args variants) = do
  -- TODO: recursion!!
  args' <- mapM evalType args
  pure (MNamed id nme args' variants)
evalType t = throwError ("unimplemented evalType for type" <> show t)
  

  

err = Except.throwError

toTopCore :: TIntTop ModulusType -> Except String TopCore  
toTopCore (TDefinition def) = TopDef <$> fromDef def
  where
    fromDef (TSingleDef name body (Just ty)) = do
      coreBody <- toCore body
      pure (SingleDef name coreBody ty)
    fromDef (TSingleDef name body Nothing) = err "definitions must be typed"

    fromDef (TOpenDef body (Just ty)) = do
      coreBody <- toCore body
      let (Signature sig) = ty
      pure (OpenDef coreBody sig)
    fromDef (TOpenDef body Nothing) = err "definitions must be typed"

    fromDef (TVariantDef nme params id alts ty) = pure (VariantDef nme params id alts ty)
toTopCore (TExpr v) = TopExpr <$> toCore v


toCore :: TIntermediate ModulusType -> Except String Core  
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
toCore (TLambda ((arg, b) : xs) body ty) = do
  sty <- case ty of 
    Just x -> pure x
    Nothing -> err "cannot convert untyped lambda"
  bodyty <- case sty of
        (MArr _ t2) -> pure t2
        (MDep _ _ t2) -> pure t2
        (ImplMDep _ _ t2) -> pure t2
        _ -> err "cannot convert badly-typed lambda"
  coreBody <- toCore (TLambda xs body (Just bodyty))
  case (b, arg) of 
    (_, BoundArg nme _) -> 
      pure (CAbs nme coreBody sty)
    (_, ValArg nme _) -> 
      pure (CAbs nme coreBody sty)
    (_, InfArg _ _) -> err "cannot convert inferred arguments!"

toCore (TLambda [] body _) = toCore body
toCore (TModule map) = do
  coreDefs <- mapM defToCore map
  pure (CMod coreDefs)
  where
    defToCore (TSingleDef nme bdy (Just ty)) = do
      bdy' <- toCore bdy
      pure (SingleDef nme bdy' ty)
    defToCore (TSingleDef nme bdy Nothing) = err "definition not typed"
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        Signature sm -> pure sm
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [ModulusType])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [ModulusType])]

  
  -- = SingleDef String Core ModulusType
  -- | VariantDef String [String] [(String, [Core])] 
  -- | EffectDef  String [String] [(String, [Core])]
  -- | OpenDef Core SigDefn

  
  -- = TVariantDef String [String] Int [(String, Int, [ModulusType])]
  -- | TEffectDef  String [String] Int [(String, Int, [ModulusType])]
  -- | TSingleDef  String TIntermediate (Maybe ModulusType)
  -- | TOpenDef TIntermediate (Maybe ModulusType)

  
toCore (TSignature map) = do
  coreDefs <- mapM defToCore map
  pure (CSig coreDefs)
  where
    defToCore (TSingleDef nme bdy t) = do
      bdy' <- toCore bdy
  -- TODO: this is bad, make sure to properly check signatures for well-formedness
      pure (SingleDef nme bdy' (TypeN 1))
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        Signature sm -> pure sm
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [ModulusType])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [ModulusType])]

toCore (TIF cond e1 e2) = do
  cond' <- toCore cond
  e1' <- toCore e1
  e2' <- toCore e2
  pure (CIF cond' e1' e2')

-- toCore x = err ("unimplemented" <> show x)



getDepType :: Value EvalM -> Maybe ModulusType
getDepType (Type t) = Just t
getDepType (Module map) =

  let map' :: Map.Map String ModulusType
      map' = Map.foldrWithKey (\k v m -> case v of
                                  Just v' -> Map.insert k v' m
                                  Nothing -> m)
                                  Map.empty (Map.map getDepType map) 
  in
    if Map.null map' then Nothing else Just (Signature map')
    
getDepType _ = Nothing
