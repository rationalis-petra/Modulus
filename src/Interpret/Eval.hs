module Interpret.Eval (Normal,
                       EvalM,
                       evalToIO,
                       eval,
                       evalTop,
                       normSubst,
                       tyApp,

                       liftFun,
                       liftFun2,
                       liftFun3,
                       liftFun4) where

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
import Interpret.Transform hiding (lift)


evalTop :: TopCore -> EvalM (Either Normal (Environment -> Environment))
evalTop (TopExpr e) = eval e >>= (\val -> pure (Left val))
evalTop (TopDef def) = case def of
  SingleDef name (CAbs sym core norm) ty -> do
    env <- ask
    let liftedFun = liftFun (\v -> local (Env.insert sym v liftedEnv) (eval core)) norm
        liftedEnv = Env.insert name liftedFun env
    val <- local liftedEnv (eval $ CAbs sym core norm)
    pure (Right (Env.insertCurrent name val))
  SingleDef name body ty -> do
    val <- eval body
    pure (Right (Env.insertCurrent name val))
  OpenDef body sig -> do
    mdle <- eval body
    case mdle of 
      NormSct m -> do
        let m' = restrict m sig 
        pure (Right (\env -> foldr (\(k, val) env -> Env.insertCurrent k val env) env m'))
      _ -> throwError "cannot open non-module"
  InductDef sym indid params ty alts -> do 
    let insertCtor env = Env.insertCurrent sym ty env
        insertAlts alts env = foldr (\(k, val) env -> Env.insertCurrent k val env) env alts

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          let alt = NormIVal sym indid id [] ty
          alts' <- mkAlts alts
          pure ((sym, alt) : alts')
          
    
    alts' <- mkAlts alts
    pure $ Right (insertCtor . insertAlts alts')
  
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
  b' <- localF (Env.insert var (Neu (NeuVar var))) (eval b)
  pure $ NormProd var a' b'

eval (CImplProd var a b) = do
  a' <- eval a
  b' <- localF (Env.insert var (Neu (NeuVar var))) (eval b)
  pure $ NormImplProd var a' b'

eval (CAbs var body ty) = do   
  body' <- localF (Env.insert var (Neu (NeuVar var))) (eval body)
  pure $ NormAbs var body' ty

eval (CApp l r) = do
  l' <- eval l
  r' <- eval r
  case l' of 
    Neu neu -> pure $ Neu (NeuApp neu r')
    NormAbs var body ty -> do
      normSubst (r', var) body
    Builtin fn ty -> fn r'
    NormIVal name tyid altid params ty -> case ty of 
      NormArr l r -> pure $ NormIVal name tyid altid (r' : params) r
      NormProd sym a b -> do
        b' <- normSubst (r', sym) b
        pure $ NormIVal name tyid altid (r' : params) b'
      NormImplProd sym a b -> do
        b' <- normSubst (r', sym) b
        pure $ NormIVal name tyid altid (r' : params) b'
      _ -> throwError ("tried to apply to non-function: " <> show l')
    other -> throwError ("tried to apply to non-function: " <> show other)

eval (CSct defs) = do
  defs' <- foldDefs defs
  pure $ NormSct $ defs'
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
                let alt = NormIVal sym indid id [] ty
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
          defs' <- localF (Env.insert var (Neu $ NeuVar var)) (foldDefs defs)
          pure ((var, val) : defs')
        _ -> throwError ("eval foldDefs not implemented for def: " <> show def)

eval (CDot ty field) = do
  ty' <- eval ty
  case ty' of 
    Neu neu ->
      pure $ Neu (NeuDot neu field)
    NormSig fields -> case getField field fields of
      Just val -> pure val
      Nothing -> throwError ("can't find field" <> field)
    NormSct fields -> case getField field fields of 
      Just val -> pure val
      Nothing -> throwError ("can't find field" <> field)
    non -> throwError ("value is not record-like" <> show non)

eval (CMatch term alts) = do
  term' <- eval term
  case term' of
    Neu neu -> neuMatch neu alts
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

    getBinds :: Normal -> Pattern -> EvalM (Maybe [(String, Normal)])
    getBinds t WildCard = pure $ Just []
    getBinds t (VarBind sym) = pure $ Just [(sym, t)]
    getBinds (NormIVal _ id1 id2 params _) (MatchInduct id1' id2' patterns) = do
      if id1 == id1' && id2 == id2' then do
        nestedBinds <- mapM (uncurry getBinds) (zip params patterns)
        let allBinds = foldr (\b a -> case (a, b) of
                                (Just a', Just b') -> Just (a' <> b')
                                _ -> Nothing) (Just []) nestedBinds
        pure allBinds
      else pure Nothing
    getBinds _ _= pure Nothing

    neuMatch :: Neutral -> [(Pattern, Core)] -> EvalM Normal
    neuMatch n ps = do
      ps' <- mapM (\(pat, core) -> do
        env <- ask
        let env' = Set.fold (\sym env -> Env.insert sym (Neu $ NeuVar sym) env) env (patVars pat)
        norm <- local env' (eval core)
        pure (pat, norm)) ps
      pure $ Neu $ NeuMatch n ps'

    getPatNeu WildCard env = env
    getPatNeu (VarBind sym) env = Env.insert sym (Neu $ NeuVar sym) env
    getPatNeu (MatchInduct id1 id2 pats) env =
      foldr getPatNeu env pats

eval (CIf cond e1 e2) = do 
  cond' <- eval cond
  case cond' of 
    Neu n -> do
      e1' <- eval e1
      e2' <- eval e2
      pure $ Neu $ NeuIf n e1' e2'
    PrimVal (Bool True) -> eval e1
    PrimVal (Bool False) -> eval e2
    _ -> throwError "eval expects condition to be bool"

eval other = throwError ("eval not implemented for" <> show other)

normSubst :: (Normal, String) -> Normal -> EvalM Normal
normSubst (val, var) ty = case ty of 
  Neu neu -> neuSubst (val, var) neu
  PrimType p -> pure $ PrimType p
  PrimVal p -> pure $ PrimVal p
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


  NormSct fields -> do
    NormSct <$> substFields (val, var) fields
  NormSig fields -> do
    NormSig <$> substFields (val, var) fields


  NormIType name id params -> do
    NormIType name id <$> mapM (normSubst (val, var)) params 
  NormIVal name tid id vals ty -> do
    vals' <- mapM (normSubst (val, var)) vals
    ty' <- normSubst (val, var) ty
    pure $ NormIVal name tid id vals' ty' 

  -- IOAction

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
  NeuVar var' ->
    if var == var' then
      pure val
    else 
      pure $ Neu (NeuVar var')
  NeuApp l r -> do
    l' <- neuSubst (val, var) l
    r' <- normSubst (val, var) r
    case l' of 
      Neu n -> pure $ Neu (NeuApp n r')
      Builtin fn ty -> fn r'
      v -> throwError ("bad app:" <> show v)

  NeuDot n field -> do
    mdle <- neuSubst (val, var) n
    case mdle of 
      Neu n -> pure $ Neu (NeuDot n field)
      NormSct fields ->
        case (getField field fields) of
          Just v -> pure v
          Nothing -> throwError ("failed to find field " <> field <> " in signature")
      NormSig fields ->
        case (getField field fields) of
          Just v -> pure v
          Nothing -> throwError ("failed to find field " <> field <> " in structure")
      v -> throwError ("bad field access: " <> show v)

  -- TODO: by "escaping" to the eval, we no longer have that Neu has no value -- bad?
  NeuMatch term pats -> do
    term' <- neuSubst (val, var) term
    case term' of
      Neu n -> do
        pats' <- mapM (\(p, e) -> do
                          if Set.member var (patVars p) then
                            pure (p, e)
                            else
                            ((,) p <$> normSubst (val, var) e)) pats
        pure $ Neu (NeuMatch n pats')
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
        getBinds t (VarBind sym) = pure $ Just [(sym, t)]
        getBinds (NormIVal _ id1 id2 params _) (MatchInduct id1' id2' patterns) = do
          if id1 == id1' && id2 == id2' then do
            nestedBinds <- mapM (uncurry getBinds) (zip params patterns)
            let allBinds = foldr (\b a -> case (a, b) of
                                    (Just a', Just b') -> Just (a' <> b')
                                    _ -> Nothing) (Just []) nestedBinds
            pure allBinds
          else pure Nothing
        getBinds _ _= pure Nothing

  NeuIf cond e1 e2 -> do
   cond' <- neuSubst (val, var) cond
   case cond' of 
     Neu n -> do
       e1' <- normSubst (val, var) e1
       e2' <- normSubst (val, var) e2
       pure $ Neu $ NeuIf n e1' e2'
     PrimVal (Bool True) -> normSubst (val, var) e1
     PrimVal (Bool False) -> normSubst (val, var) e2
     _ -> throwError ("bad condition in if: expected bool, got: " <> show cond')
     


  NeuBuiltinApp fn neu ty -> do
    arg <- neuSubst (val, var) neu
    case arg of 
      Neu neu -> pure $ Neu $ NeuBuiltinApp fn neu ty
      _ -> (fn arg)
      
  NeuBuiltinApp2 fn neu ty -> do
    arg <- neuSubst (val, var) neu
    case arg of 
      Neu neu -> pure $ Neu $ NeuBuiltinApp2 fn neu ty
      _ -> pure (liftFun (fn arg) ty)

  NeuBuiltinApp3 fn neu ty -> do
    arg <- neuSubst (val, var) neu
    case arg of 
      Neu neu -> pure $ Neu $ NeuBuiltinApp3 fn neu ty
      _ -> pure (liftFun2 (fn arg) ty)

  NeuBuiltinApp4 fn neu ty -> do
    arg <- neuSubst (val, var) neu
    case arg of 
      Neu neu -> pure $ Neu $ NeuBuiltinApp4 fn neu ty
      _ -> pure (liftFun3 (fn arg) ty)


  -- NeuDot sig field -> do
  --   sig' <- neuSubst 

tyApp :: Normal -> Normal -> EvalM Normal
tyApp (NormArr l r) _ = pure r 
tyApp (NormProd sym a b) arg = normSubst (arg, sym) b
tyApp (NormImplProd sym a b) arg = normSubst (arg, sym) b



instance Eq (Normal' m) where
  a == b = norm_equiv a b (Set.empty, 0) (Map.empty, Map.empty)


-- TODO: add Î· reductions to the equality check
norm_equiv :: (Normal' m) -> (Normal' m) -> Generator -> (Map.Map String String, Map.Map String String) -> Bool 
norm_equiv (NormUniv n1) (NormUniv n2) gen rename = n1 == n2
norm_equiv (Neu n1) (Neu n2) gen rename = neu_equiv n1 n2 gen rename
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
neu_equiv (NeuVar v1) (NeuVar v2) used (lrename, rrename) =
  case (Map.lookup v1 lrename, Map.lookup v2 rrename) of
    (Just v1', Just v2') -> v1 == v2
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
      putStrLn $ "err: " <> err
      return Nothing
  where
    accumEffects :: EvalM Normal -> (Normal -> EvalM a) -> ProgState -> IO (Maybe (a, ProgState))
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
          putStrLn $ "error: " <> err
          return Nothing


interceptNeutral :: (Normal -> EvalM Normal) -> Normal -> Normal -> EvalM Normal
interceptNeutral f ty (Neu neutral) = pure $ Neu (NeuBuiltinApp (interceptNeutral f ty) neutral ty)
interceptNeutral f ty val = f val


-- liftFun needs to intercept /neutral/ terms!
liftFun :: (Normal -> EvalM Normal) -> Normal -> Normal
liftFun f ty = Builtin (interceptNeutral f ty) ty

liftFun2 :: (Normal -> Normal -> EvalM Normal) -> Normal -> Normal
liftFun2 f ty =
  let f' = f in
    Builtin (\val -> case val of
                (Neu neu) -> pure $ Neu $ NeuBuiltinApp2 f neu ty
                _ ->
                  case ty of
                    (NormArr _ r) -> pure $ liftFun (f' val) r
                    (NormProd var _ body) -> pure $ liftFun (f' val) body
                    (NormImplProd var _ body) -> pure $ liftFun (f' val) body)
    ty

liftFun3 :: (Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun3 f ty =
  let f' = f in
    Builtin (\val -> case val of
                (Neu neu) -> pure $ Neu $ NeuBuiltinApp3 f neu ty
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun2 (f' val) r
                  (NormProd var _ body) -> pure $ liftFun2 (f' val) body
                  (NormImplProd var _ body) -> do pure $ liftFun2 (f' val) body)
    ty

liftFun4 :: (Normal -> Normal -> Normal -> Normal -> EvalM Normal) -> Normal -> Normal 
liftFun4 f ty =
  let f' = f in
    Builtin (\val -> case val of
                (Neu neu) -> pure $ Neu $ NeuBuiltinApp4 f neu ty
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun3 (f val) r
                  (NormProd var _ body) -> pure $ liftFun3 (f val) body
                  (NormImplProd var _ body) -> pure $ liftFun3 (f val) body)
    ty



