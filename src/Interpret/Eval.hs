module Interpret.Eval (Normal,
                       EvalM,
                       evalToIO,
                       eval,
                       evalTop,
                       normSubst,
                       tyApp,
                       Result(..),
                       neu_equiv,
                       liftFun,
                       liftFun2,
                       liftFun3,
                       liftFun4,
                       liftFun5,
                       liftFun6) where

import Prelude hiding (lookup)

import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Interpret.Environment as Env

import Syntax.Utils  
import Interpret.EvalM
  
import Data
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vector
import Interpret.Transform hiding (lift)

  
data Result
  = RValue Normal
  | RDef (Environment -> Environment)
  | RAnn String Normal


evalTop :: TopCore -> EvalM Result
evalTop (TopExpr e) = eval e >>= (\val -> pure (RValue val))
evalTop (TopDef def) = case def of
  SingleDef name (CAbs sym core norm) ty -> do
    env <- ask
    let liftedFun = liftFun (\v -> local (Env.insert sym v liftedEnv) (eval core)) norm
        liftedEnv = Env.insert name liftedFun env
    val <- local liftedEnv (eval $ CAbs sym core norm)
    pure (RDef (Env.insertCurrent name val))
  SingleDef name body ty -> do
    val <- eval body
    pure (RDef (Env.insertCurrent name val))
  OpenDef body sig -> do
    mdle <- eval body
    case mdle of 
      NormSct m (NormSig ty) -> do
        let m' = (restrict (restrict m ty) sig)
        pure (RDef (\env -> foldr (\(k, val) env -> Env.insertCurrent k val env) env m'))
      _ -> throwError "cannot open non-module"
  InductDef sym indid params ty alts -> do 
    let insertCtor env = Env.insertCurrent sym ty env
        insertAlts alts env = foldr (\(k, val) env -> Env.insertCurrent k val env) env alts

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          let alt = NormIVal sym indid id (length params) [] ty
          alts' <- mkAlts alts
          pure ((sym, alt) : alts')
          
    
    alts' <- mkAlts alts
    pure $ RDef (insertCtor . insertAlts alts')
  CoinductDef sym coid params ty alts -> do 
    let insertCtor env = Env.insertCurrent sym ty env
        insertAlts alts env = foldr (\(k, val) env -> Env.insertCurrent k val env) env alts

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          let alt = NormCoDtor sym coid id (tySize ty) (length params) [] ty
          alts' <- mkAlts alts
          pure ((sym, alt) : alts')

        tySize (NormArr l r) = 1 + tySize r
        tySize (NormProd _ _ r) = 1 + tySize r
        tySize (NormImplProd _ _ r) = 1 + tySize r
        tySize _ = 0
    
    alts' <- mkAlts alts
    pure $ RDef (insertCtor . insertAlts alts')
evalTop (TopAnn sym term) = do
  term' <- eval term
  pure (RAnn sym term')

  
-- evaluate an expression, to a normal form (not a value!). This means that the
-- environment now contains only normal forms!
eval :: Core -> EvalM Normal
eval (CNorm n) = pure n
eval (CVar var) = do
  env <- ask
  case Env.lookup var env of 
    Just val -> pure val
    Nothing -> throwError ("could not find variable " <> var <> " in context")

eval (CArr l r) = do
  l' <- eval l
  r' <- eval r
  pure $ NormArr l' r'
  
eval (CProd var a b) = do
  a' <- eval a
  let ty = (NormUniv 0)
  b' <- localF (Env.insert var (Neu (NeuVar var ty) ty)) (eval b)
  pure $ NormProd var a' b'

eval (CImplProd var a b) = do
  a' <- eval a
  let ty = (NormUniv 0)
  b' <- localF (Env.insert var (Neu (NeuVar var ty) ty)) (eval b)
  pure $ NormImplProd var a' b'

eval (CAbs var body ty) = do   
  hd <- tyHead ty
  body' <- localF (Env.insert var (Neu (NeuVar var hd) hd)) (eval body)
  pure $ NormAbs var body' ty

eval (CApp l r) = do
  l' <- eval l
  r' <- eval r
  case l' of 
    Neu neu ty -> do
      tr <- liftExcept (typeVal r')
      ty' <- tyApp ty tr
      pure $ Neu (NeuApp neu r') ty'
    NormAbs var body ty -> normSubst (r', var) body
    Builtin fn ty -> fn r'
    NormIVal name tyid altid strip params ty -> do
      ty' <- tyApp ty r'
      pure $ NormIVal name tyid altid strip (r' : params) ty'
    NormCoDtor name id1 id2 len strip args ty -> do
      ty' <- tyApp ty r'
      case len of 
        0 -> throwError "too many arugments to destructor"
        1 -> applyDtor id1 id2 strip (reverse (r' : args))
        _ -> pure $ NormCoDtor name id1 id2 (len - 1) strip (r' : args) ty
    InbuiltCtor ctor -> case ctor of   
      IndPat _ _ _ n _ -> eval (CApp (CNorm n) (CNorm r'))

    other -> throwError ("tried to apply to non-function: " <> show other)

eval (CSct defs ty) = do
  defs' <- foldDefs defs
  pure $ NormSct defs' ty
  where
    foldDefs :: [Definition] -> EvalM  [(String, Normal)]
    foldDefs [] = pure []
    foldDefs (def : defs) = do
      case def of  
        SingleDef var core ty -> do
          val <- eval core
          defs' <- localF (Env.insert var val) (foldDefs defs)
          pure ((var, val) : defs')
        InductDef sym indid params ty alts -> do
          let mkAlts [] = []
              mkAlts ((sym, id, ty) : alts) =
                let alt = NormIVal sym indid id (length params) [] ty
                    alts' = mkAlts alts
                in ((sym, alt) : alts')
          pure ((sym, ty) : mkAlts alts)

eval (CSig defs) = do
  defs' <- foldDefs defs
  pure $ NormSig $ defs'
  where
    foldDefs :: [Definition] -> EvalM  [(String, Normal)]
    foldDefs [] = pure []
    foldDefs (def : defs) = do
      case def of
        SingleDef var core ty -> do
          val <- eval core
  -- TODO: is this really the solution? perhaps. 
          defs' <- localF (Env.insert var (Neu (NeuVar var ty) ty)) (foldDefs defs)
          pure ((var, val) : defs')
        _ -> throwError ("eval foldDefs not implemented for def: " <> show def)

eval (CDot term field) = do
  val <- eval term
  case val of
    Neu neu ty -> do
      ty <- tyField field ty
      pure $ Neu (NeuDot neu field) ty
    NormSig fields -> case getField field fields of
      Just val -> pure val
      Nothing -> throwError ("can't find field" <> field)
    -- TODO: restrict by field
    NormSct fields ty -> case getField field fields of 
      Just val -> pure val
      Nothing -> throwError ("can't find field" <> field)
    non -> throwError ("value is not record-like" <> show non)

eval (CMatch term alts ty) = do
  term' <- eval term
  case term' of
    Neu neu _ -> neuMatch neu alts
    _ -> match term' alts
  where 
    match t [] = throwError ("couldn't match value: " <> show t)
    match t ((pat, expr) : as) = do
      binds <- getBinds t pat
      case binds of
        Just b -> do
          env <- ask
          let env' = foldr (\(sym, val) env -> Env.insert sym val env) env b
          local env' (eval expr)
        Nothing -> match t as

    -- Take a value and a pattern. If the value matches the pattern, return a
    --   list of what variables to bind 
    --   otherwise, return none
    getBinds :: Normal -> Pattern -> EvalM (Maybe [(String, Normal)])
    getBinds t WildCard = pure $ Just []
    getBinds t (VarBind sym _) = pure $ Just [(sym, t)]
    getBinds (NormIVal _ id1 id2 strip params _) (MatchInduct id1' id2' patterns) = do
      if id1 == id1' && id2 == id2' then do
        nestedBinds <- mapM (uncurry getBinds) (zip (drop strip params) patterns)
        let allBinds = foldr (\b a -> case (a, b) of
                                (Just a', Just b') -> Just (a' <> b')
                                _ -> Nothing) (Just []) nestedBinds
        pure allBinds
      else pure Nothing
    getBinds n (InbuiltMatch fun) = fun n getBinds
    getBinds _ _= pure Nothing

    -- construct a neutral matching term.
    neuMatch :: Neutral -> [(Pattern, Core)] -> EvalM Normal
    neuMatch n ps = do
      ps' <- mapM (\(pat, core) -> do
        env <- ask
        let env' = getPatNeu pat env
        norm <- local env' (eval core)
        pure (pat, norm)) ps
      pure $ Neu (NeuMatch n ps' ty) ty

    getPatNeu WildCard env = env
    getPatNeu (VarBind sym ty) env = Env.insert sym (Neu (NeuVar sym ty) ty) env
    getPatNeu (MatchInduct id1 id2 pats) env = foldr getPatNeu env pats

eval (CCoMatch patterns ty) = do 
  funcs <- mapM evalCoPat patterns 
  pure $ NormCoVal funcs ty
  where
    evalCoPat (pat, body)  = do 
      env <- ask
      pure (pat, (local (getPatNeu pat env) (eval body)))

    getPatNeu CoWildCard env = env
    getPatNeu (CoVarBind sym ty) env = Env.insert sym (Neu (NeuVar sym ty) ty) env
    getPatNeu (CoMatchInduct _ _ _ pats) env = foldr getPatNeu env pats



eval (CIf cond e1 e2 ty) = do 
  cond' <- eval cond
  case cond' of 
    Neu n _ -> do
      e1' <- eval e1
      e2' <- eval e2
      pure $ Neu (NeuIf n e1' e2' ty) ty
    PrimVal (Bool True) -> eval e1
    PrimVal (Bool False) -> eval e2
    _ -> throwError "eval expects condition to be bool"

eval other = throwError ("eval not implemented for" <> show other)

normSubst :: (Normal, String) -> Normal -> EvalM Normal
normSubst (val, var) ty = case ty of 
  Neu neu ty -> neuSubst (val, var) neu
  PrimType p -> pure $ PrimType p
  PrimVal p -> pure $ PrimVal p
  CollTy cty -> case cty of 
    MaybeTy a -> (CollTy . MaybeTy) <$> normSubst (val, var) a
    ListTy a -> (CollTy . ListTy) <$> normSubst (val, var) a
    ArrayTy a dims -> CollTy <$> (ArrayTy <$> normSubst (val, var) a <*> pure dims)
    IOMonadTy a -> (CollTy . IOMonadTy) <$> normSubst (val, var) a
  CollVal cvl -> case cvl of 
    MaybeVal m ty -> case m of 
      Just some -> CollVal <$> (MaybeVal <$> (Just <$> (normSubst (val, var) some))
                                <*> normSubst (val, var) ty)
      Nothing -> CollVal <$> (MaybeVal Nothing <$> normSubst (val, var) ty)
    ListVal vals ty -> CollVal <$> (ListVal <$> mapM (normSubst (val, var)) vals <*> normSubst (val, var) ty)
    ArrayVal vec ty shape -> CollVal <$> (ArrayVal <$> Vector.mapM (normSubst (val, var)) vec
                                      <*> normSubst (val, var) ty <*> pure shape)
    IOAction fn ty -> (CollVal . IOAction fn) <$> normSubst (val, var) ty  
  NormCoVal pats ty -> do
    let pats' = map substCoPat pats
    ty' <- normSubst (val, var) ty
    pure (NormCoVal pats' ty')
    where 
      substCoPat :: (CoPattern, EvalM Normal) -> (CoPattern, EvalM Normal)
      substCoPat (copattern, body) = do
        let vars = getCoPatVars copattern in
          if Set.member var vars then
            (copattern, body)
          else
            (copattern, (body >>= normSubst (val, var)))

      getCoPatVars :: CoPattern -> Set.Set String
      getCoPatVars CoWildCard = Set.empty
      getCoPatVars (CoVarBind var _) = Set.singleton var
      getCoPatVars (CoMatchInduct _ _ _ subPatterns) =
        foldr (Set.union . getCoPatVars) Set.empty subPatterns

 
  NormUniv n -> pure $ NormUniv n

  
  NormProd var' a b ->
    if var == var' then  do
      a' <- normSubst (val, var) a
      pure $ NormProd var' a' b
    else do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormProd var' a' b'
  NormImplProd var' a b -> 
    if var == var' then  do
      a' <- normSubst (val, var) a
      pure $ NormImplProd var' a' b
    else do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormImplProd var' a' b'
  NormArr a b -> do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormArr a' b'
  NormAbs var' body ty -> do 
    if var == var' then  do
      ty' <- normSubst (val, var) ty
      pure $ NormAbs var' body ty'
    else do
      body' <- normSubst (val, var) body
      ty' <- normSubst (val, var) ty
      pure $ NormAbs var' body' ty'


  NormSct fields ty -> do
    NormSct <$> substFields (val, var) fields <*> normSubst (val, var) ty
  NormSig fields -> do
    NormSig <$> substFields (val, var) fields


  NormIType name id params -> do
    NormIType name id <$> mapM (normSubst (val, var)) params 
  NormIVal name tid id strip vals ty -> do
    vals' <- mapM (normSubst (val, var)) vals
    ty' <- normSubst (val, var) ty
    pure $ NormIVal name tid id strip vals' ty' 

  BuiltinMac m -> pure $ BuiltinMac m
  Special sp   -> pure $ Special sp
  Keyword key  -> pure $ Keyword key
  Symbol sym   -> pure $ Symbol sym
  AST ast      -> pure $ AST ast


  -- Undef 
  s -> throwError ("subst not implemented for: " <> show s)
  where 
    substFields :: (Normal, String) -> [(String, Normal)] -> EvalM [(String, Normal)]
    substFields (val, var) ((var', val') : fields) = do
      if var == var' then 
        pure $ (var', val') : fields
      else do
        val'' <- normSubst (val, var) val'
        fields' <- substFields (val, var) fields 
        pure $ (var', val'') : fields'
    substFields (val, var) [] = pure []

  
neuSubst :: (Normal, String) -> Neutral -> EvalM Normal
neuSubst (val, var) neutral = case neutral of 
  NeuVar var' ty ->
    if var == var' then
      pure val
    else 
      pure $ Neu (NeuVar var' ty) ty
  NeuApp l r -> do
    l' <- neuSubst (val, var) l
    r' <- normSubst (val, var) r
    case l' of 
      Neu n ty -> do
        ty' <- tyApp ty r'
        pure $ Neu (NeuApp n r') ty'
      Builtin fn ty -> fn r'
      v -> throwError ("bad app:" <> show v)

  NeuDot n field -> do
    mdle <- neuSubst (val, var) n
    case mdle of 
      Neu n ty -> do
        ty' <- tyField field ty
        pure $ Neu (NeuDot n field) ty'
  -- TODO: restrict by ty
      NormSct fields ty ->
        case (getField field fields) of
          Just v -> pure v
          Nothing -> throwError ("failed to find field " <> field <> " in signature")
      NormSig fields ->
        case (getField field fields) of
          Just v -> pure v
          Nothing -> throwError ("failed to find field " <> field <> " in structure")
      v -> throwError ("bad field access: " <> show v)

  -- TODO: by "escaping" to the eval, we no longer have that Neu has no value -- bad?
  NeuMatch term pats ty -> do
    term' <- neuSubst (val, var) term
    case term' of
      Neu n _ -> do
        pats' <- mapM (\(p, e) -> do
                          if Set.member var (patVars p) then
                            pure (p, e)
                            else
                            ((,) p <$> normSubst (val, var) e)) pats
        pure $ Neu (NeuMatch n pats' ty) ty
      term -> match term pats

     where
        match t [] = throwError ("couldn't match value: " <> show t)
        match t ((pat, expr) : as) = do
          binds <- getBinds t pat
          case binds of
            Just b -> do
              expr' <- foldBinds b expr
              normSubst (val, var) expr'
              where
                foldBinds ((var, val) : bs) expr = normSubst (val, var) expr >>= foldBinds bs
                foldBinds [] expr = pure expr
            Nothing -> match t as
    
        getBinds :: Normal -> Pattern -> EvalM (Maybe [(String, Normal)])
        getBinds t WildCard = pure $ Just []
        getBinds t (VarBind sym _) = pure $ Just [(sym, t)]
        getBinds (NormIVal _ id1 id2 strip params _) (MatchInduct id1' id2' patterns) = do
          if id1 == id1' && id2 == id2' then do
            nestedBinds <- mapM (uncurry getBinds) (zip (drop strip params) patterns)
            let allBinds = foldr (\b a -> case (a, b) of
                                    (Just a', Just b') -> Just (a' <> b')
                                    _ -> Nothing) (Just []) nestedBinds
            pure allBinds
          else pure Nothing
        getBinds _ _= pure Nothing

  NeuIf cond e1 e2 ty -> do
   cond' <- neuSubst (val, var) cond
   case cond' of 
     Neu n _ -> do
       e1' <- normSubst (val, var) e1
       e2' <- normSubst (val, var) e2
       pure $ Neu (NeuIf n e1' e2' ty) ty
     PrimVal (Bool True) -> normSubst (val, var) e1
     PrimVal (Bool False) -> normSubst (val, var) e2
     _ -> throwError ("bad condition in if: expected bool, got: " <> show cond')
     


  NeuBuiltinApp fn neu ty -> do
    arg <- neuSubst (val, var) neu
    (fn arg)

  -- NeuDot sig field -> do
  --   sig' <- neuSubst 
tyHead :: Normal -> EvalM Normal
tyHead (NormArr l r) = pure l
tyHead (NormProd sym a b) = pure a
tyHead (NormImplProd sym a b) = pure b
tyHead hd = throwError ("can't get type head of " <> show hd)

tyField :: String -> Normal -> EvalM Normal  
tyField field (NormSig fields) =
  case getField field fields of
    Just x -> pure x
    Nothing -> throwError ("can't find field: " <> field)
tyField field (NormSct fields _) =
  case getField field fields of
    Just x -> pure x
    Nothing -> throwError ("can't find field: " <> field)

tyApp :: Normal -> Normal -> EvalM Normal
tyApp (NormArr l r) _ = pure r 
tyApp (NormProd sym a b) arg = normSubst (arg, sym) b
tyApp (NormImplProd sym a b) arg = normSubst (arg, sym) b



instance Eq (Normal' m) where
  a == b = norm_equiv a b (Set.empty, 0) (Map.empty, Map.empty)


-- TODO: add Î· reductions to the equality check
norm_equiv :: (Normal' m) -> (Normal' m) -> Generator -> (Map.Map String String, Map.Map String String) -> Bool 
norm_equiv (NormUniv n1) (NormUniv n2) gen rename = n1 == n2
norm_equiv (Neu n1 _) (Neu n2 _) gen rename = neu_equiv n1 n2 gen rename
norm_equiv (PrimVal p1) (PrimVal p2) _ _ = p1 == p2
norm_equiv (PrimType p1) (PrimType p2) _ _ = p1 == p2

-- Note: arrows and dependent types /can/ be equivalent if the bound variable
-- doesn't come on the LHS
norm_equiv (NormProd var a b) (NormProd var' a' b') gen (lrename, rrename) = 
  let (nvar, gen') = genFresh gen
  in (a == a') && (norm_equiv b b'
                   (useVars [var, var', nvar] gen')
                   (Map.insert var nvar lrename, Map.insert var' nvar rrename))
norm_equiv (NormArr a b)     (NormArr a' b') gen rename = 
  (norm_equiv a a' gen rename) || (norm_equiv b b' gen rename)
norm_equiv (NormProd var a b) (NormArr a' b') gen rename = 
  if Set.member var (free b) then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename
norm_equiv (NormArr  a b) (NormProd var' a' b') gen rename = 
  if Set.member var' (free b') then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename
-- norm_equiv (NormImplProd var a b) (NormImplProd var' a' b') gen rename = 
--   (var a b) || ()



  
neu_equiv :: (Neutral' m) -> (Neutral' m) -> Generator -> (Map.Map String String, Map.Map String String)
        -> Bool 
neu_equiv (NeuVar v1 _) (NeuVar v2 _) used (lrename, rrename) =
  case (Map.lookup v1 lrename, Map.lookup v2 rrename) of
    (Just v1', Just v2') -> v1' == v2'
    (Nothing, Nothing) -> v1 == v2
    (_, _) -> False
neu_equiv (NeuApp l1 r1) (NeuApp l2 r2) used rename = 
  (neu_equiv l1 l2 used rename) && (norm_equiv r1 r2 used rename)
neu_equiv (NeuDot neu1 field1) (NeuDot neu2 field2) used rename
  = (field1 == field2) && neu_equiv neu1 neu2 used rename 





type Generator = (Set.Set String, Int)  

useVar :: String -> Generator -> Generator  
useVar var (set, id) = (Set.insert var set, id)

useVars :: [String] -> Generator -> Generator  
useVars vars (set, id) = (foldr Set.insert set vars, id)

  
genFresh :: Generator -> (String, Generator)
genFresh (set, id) =
  let var = ("#" <> show id)
  in
    if Set.member var set then
      genFresh (set, id+1)
    else
      (var, (Set.insert var set, id+1))

evalToIO :: EvalM a -> Environment -> ProgState -> IO (Maybe (a, ProgState))
evalToIO inner_mnd ctx state =
  case runState (runExceptT (runReaderT inner_mnd ctx)) state of
    (Right obj, state') -> do
      return $ Just (obj, state')
    (Left err, state') -> do
      putStrLn $ "err: " <> err
      return Nothing

-- evalToIO :: EvalM a -> Environment -> ProgState -> IO (Maybe (a, ProgState))
-- evalToIO (ActionMonadT inner_mnd) ctx state =
--   case runState (runExceptT (runReaderT inner_mnd ctx)) state of
--     (Right (Value obj), state') -> do
--       return $ Just (obj, state')
--     (Right (RaiseAction cnt id1 id2 args (Just f)), state') -> do
--       result <- f args
--       accumEffects result cnt state'
--     (Right (RaiseAction cnt id1 id2 args Nothing), state') -> do
--       putStrLn $ "Action Called Without Being Handled: ("  ++ show id2 ++ "," ++ show id2 ++ ")"
--       return Nothing
--     (Left err, state') -> do
--       putStrLn $ "err: " <> err
--       return Nothing
--   where
--     accumEffects :: EvalM Normal -> (Normal -> EvalM a) -> ProgState -> IO (Maybe (a, ProgState))
--     accumEffects (ActionMonadT inner_mnd) cnt state = 
--       case runState (runExceptT (runReaderT inner_mnd ctx)) state of
--         (Right (RaiseAction cnt2 id1 id2 args (Just f)), state') -> do 
--           result <- f args
--           accumEffects result (\x -> cnt2 x >>= cnt) state'
--         (Right (Value obj), state') -> do
--           evalToIO (cnt obj) ctx state'
--         (Right (RaiseAction _ id1 id2 _ Nothing), state') -> do
--           putStrLn $ "Action Called Without Default" ++ show (id1, id2)
--           return Nothing
--         (Left err, state') -> do
--           putStrLn $ "error: " <> err
--           return Nothing

-- evalToIO :: EvalM a -> Environment -> ProgState -> IO (Maybe (a, ProgState))
-- evalToIO (ActionMonadT inner_mnd) ctx state =
--   case runState (runExceptT (runReaderT inner_mnd ctx)) state of
--     (Right (Value obj), state') -> do
--       return $ Just (obj, state')
--     (Right (RaiseAction cnt id1 id2 args (Just f)), state') -> do
--       result <- f args
--       accumEffects result cnt state'
--     (Right (RaiseAction cnt id1 id2 args Nothing), state') -> do
--       putStrLn $ "Action Called Without Being Handled: ("  ++ show id2 ++ "," ++ show id2 ++ ")"
--       return Nothing
--     (Left err, state') -> do
--       putStrLn $ "err: " <> err
--       return Nothing
--   where
--     accumEffects :: EvalM Normal -> (Normal -> EvalM a) -> ProgState -> IO (Maybe (a, ProgState))
--     accumEffects (ActionMonadT inner_mnd) cnt state = 
--       case runState (runExceptT (runReaderT inner_mnd ctx)) state of
--         (Right (RaiseAction cnt2 id1 id2 args (Just f)), state') -> do 
--           result <- f args
--           accumEffects result (\x -> cnt2 x >>= cnt) state'
--         (Right (Value obj), state') -> do
--           evalToIO (cnt obj) ctx state'
--         (Right (RaiseAction _ id1 id2 _ Nothing), state') -> do
--           putStrLn $ "Action Called Without Default" ++ show (id1, id2)
--           return Nothing
--         (Left err, state') -> do
--           putStrLn $ "error: " <> err
--           return Nothing


interceptNeutral :: (Normal -> EvalM Normal) -> Normal -> Normal -> EvalM Normal
interceptNeutral f ty (Neu neutral nty) = do
  ty' <- tyApp ty nty
  pure $ Neu (NeuBuiltinApp (interceptNeutral f ty) neutral ty') ty'
interceptNeutral f ty val = f val


-- liftFun needs to intercept /neutral/ terms!
liftFun :: (Normal -> EvalM Normal) -> Normal -> Normal
liftFun f ty = Builtin (interceptNeutral f ty) ty

liftFun2 :: (Normal -> Normal -> EvalM Normal) -> Normal -> Normal
liftFun2 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ ->
                  case ty of
                    (NormArr _ r) -> pure $ liftFun (f val) r
                    (NormProd var _ body) -> pure $ liftFun (f val) body
                    (NormImplProd var _ body) -> pure $ liftFun (f val) body
  in Builtin f' ty

liftFun3 :: (Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun3 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun2 (f val) r
                  (NormProd var _ body) -> pure $ liftFun2 (f val) body
                  (NormImplProd var _ body) -> do pure $ liftFun2 (f val) body
  in Builtin f' ty

liftFun4 :: (Normal -> Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun4 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun3 (f val) r
                  (NormProd var _ body) -> pure $ liftFun3 (f val) body
                  (NormImplProd var _ body) -> pure $ liftFun3 (f val) body
  in Builtin f' ty

liftFun5 :: (Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun5 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun4 (f val) r
                  (NormProd var _ body) -> pure $ liftFun4 (f val) body
                  (NormImplProd var _ body) -> pure $ liftFun4 (f val) body
    in Builtin f' ty

liftFun6 :: (Normal -> Normal -> Normal -> Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun6 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun5 (f val) r
                  (NormProd var _ body) -> pure $ liftFun5 (f val) body
                  (NormImplProd var _ body) -> pure $ liftFun5 (f val) body
    in Builtin f' ty

  
applyDtor :: Int -> Int -> Int -> [Normal] -> EvalM Normal
applyDtor id1 id2 strip (arg:args) 
  | strip == 0 = case arg of 
      NormCoVal patterns _ -> go args patterns
      _ -> throwError "bad destructor application"
  | otherwise = applyDtor id1 id2 (strip - 1) args

  
  where go args [] = throwError "cannot find appropriate copattern in coinductive value"
        go args ((p, body) : ps) = case getBindList p args of 
          Just binds -> 
            foldr (\(str, val) term -> (term >>= normSubst (val, str)))
                  body
                  binds
          Nothing -> go args ps

        getBindList a args = case a of 
          CoMatchInduct _ id1' id2' subPatterns ->
            if id1' == id1 && id2' == id2 then
              foldr (\pair accum -> case (getBinds pair, accum) of
                                      (Just xs, Just ys) -> Just (xs <> ys)
                                      _ -> Nothing) (Just []) (zip subPatterns args)
            else Nothing 
              

        getBinds (p, arg) = case p of 
          CoWildCard -> Just []
          CoVarBind sym _ -> Just [(sym, arg)]



applyDtor _ _ _ _ = throwError "bad destructor application"  
