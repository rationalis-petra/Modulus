module Interpret.Eval (Expr,
                       EvalM,
                       eval,
                       evalTopLevel,
                       evalToIO,

                       liftFun,
                       liftFun2,
                       liftFun3,
                       liftFun4) where

import Prelude hiding (lookup)

import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Control.Lens as Lens -- ((+=), use)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State
import qualified Interpret.Context as Context
import qualified Interpret.Transform as Action
import Typecheck.TypeUtils(isLarge)

import Interpret.EvalM
  
import Data
import qualified Data.Map as Map
import Interpret.Transform hiding (lift)



eval :: Intermediate -> EvalM Expr
eval (IValue (CustomCtor 0 lst ctor _ _)) = ctor lst
eval (IValue e) = pure e
eval (IQuote e) = pure (AST e)
eval (IAccess e s) = do
  result <- eval e 
  case result of 
    Module m -> case Map.lookup s m of  
      Just x -> pure x
      Nothing -> throwError ("could not find field " <> s)
  -- TODO: figure out a better way to do this?
    Type t -> pure (Type (MDot t s))
    _ -> throwError ("tried to get field " <> s <> " from a non-module")
eval (ISymbol s) = do
  ctx <- ask
  case Context.lookup s ctx of 
    Just val -> pure val
    Nothing -> throwError ("could not find symbol " ++ s)
eval (IApply op arg) = do
  fnc <- eval op
  case fnc of 
    InbuiltFun f _ -> do
      arg' <- eval arg
      f arg'
    Function [] body fn_ctx -> 
        throwError "Function has empty arg-list!" 
    Function (var : vars) body fn_ctx ->  do
          arg <- eval arg
          let new_ctx = case var of
                "_" -> fn_ctx
                _ -> Context.insert var arg fn_ctx
          if null vars then
            local new_ctx (eval body)
          else 
            pure $ Function vars body new_ctx

    Constructor nme id var nargs curr -> do 
      arg' <- eval arg
      case nargs of 
        n | n == 0 -> throwError "constructor with 0 args not callable!"
          | n == 1 -> pure $ Variant nme id var (reverse (arg' : curr))
          | otherwise -> pure $ Constructor nme id var (n-1) (arg' : curr)

    CustomCtor nargs lst ctor dtor t -> do 
      arg' <- eval arg
      case nargs of 
        n | n == 0 -> throwError "constructor with 0 args not callable!"
          | n == 1 -> ctor (arg' : lst)
          | otherwise -> pure $ CustomCtor (nargs-1) (arg':lst) ctor dtor t

    Action effid id nargs curr -> do
      arg' <- eval arg
      case nargs of 
        n | n == 0 -> throwError "action with 0 args not callable!"
          | n == 1 -> raise effid id (arg' : curr) Nothing
          | otherwise -> pure $ Action effid id (nargs - 1) (arg' : curr)


    IOAction id nargs def curr -> do
      arg' <- eval arg
      case nargs of 
        n | n == 0 -> throwError "action with 0 args not callable!"
          -- TODO: technically works, but feels wrong to use eid=0
          | n == 1 -> raise 0 id (arg' : curr) (Just def)
          | otherwise -> pure $ IOAction id (nargs - 1) def (arg' : curr)

    _  -> throwError ("eval called an object which is not a function: " ++ show fnc)


eval (ILambda args body) = do
  ctx <- ask
  pure $ Function (deAnn (map (\(f, _) -> f) args)) body ctx
eval (IMacro args body) = do
  ctx <- ask
  pure $ Macro (deAnn args) body ctx
eval (ILet binds body) = do
  -- TODO: make the let-binding recursive by replacing the value e in each
  -- binding [x e] with a function [x () -> e]. Further, in the body of each of
  -- these e's, recursively bound variables bound variables x are replaced with
  -- function-calls [x ()]
  ctx <- ask
  let (syms, code) = unzip binds
  vals <- mapM (\x -> eval x) code
  let new_ctx =
        foldr (\(sym, val) ctx -> Context.insert sym val ctx)
            ctx (zip syms new_vals)
      new_vals = map (\x -> updateVal x new_ctx) vals
      updateVal (Function args body old_ctx) ctx = (Function args body ctx)
      updateVal x ctx = x
  local new_ctx (eval body) 

eval (ILetOpen md body) = do
  ctx <- ask
  modules <- mapM (\x -> eval x) md 
  newCtx <- addToCtx modules ctx
  local newCtx (eval body)

  where
    addToCtx :: [Expr] -> Context -> EvalM Context
    addToCtx [] ctx = pure ctx
    addToCtx (m : ms) ctx = do
      newCtx <- (foldModule m ctx)
      addToCtx ms newCtx

    foldModule :: Expr -> Context -> EvalM Context
    foldModule mod ctx = 
      case mod of 
        Module binds ->
          pure $ Map.foldrWithKey (\sym val ctx -> Context.insert sym val ctx)
                 ctx binds
        _ -> throwError "let-open expects modules in first argument"
  
eval (IIF cond e1 e2) = do
  cond' <- eval cond 
  case cond' of 
    PrimE (Bool True)  -> eval e1 
    PrimE (Bool False) -> eval e2 
    _ -> throwError "non-boolean condition in if"

  
eval (IModule deflist) =  do
  ctx <- ask
  defs <- foldDefs deflist ctx
  let defs' = map (\(str, val) -> (str, val)) defs in
    pure $ Module (Map.fromList defs')
  where
    foldDefs :: [IDefinition] -> Context -> EvalM [(String, Expr)]
    foldDefs [] ctx = pure []
    foldDefs (x : xs) ctx = do
      defs <- local ctx (runDefinition x)
      let newCtx = addToCtx defs ctx
      rest <- foldDefs xs newCtx
      return (defs <> rest)

    addToCtx [] ctx = ctx
    addToCtx ((str, val) : defs) ctx = 
      let newCtx = Context.insert str val ctx in
        addToCtx defs newCtx
      
eval (ISignature deflist) =  do
  ctx <- ask
  defs <- foldDefs deflist ctx
  defs' <- mapM checkSigDef defs
  pure $ Type (Signature (Map.fromList defs'))
  where
    checkSigDef :: (String, Expr) -> EvalM (String, ModulusType)
    checkSigDef (str, obj) = 
      case obj of 
        Type t -> pure (str, t)
        _ -> throwError "signatures expect only types in their defs"
    
    foldDefs :: [IDefinition] -> Context -> EvalM [(String, Expr)]
    foldDefs [] ctx = pure []
    foldDefs (x : xs) ctx = do
      defs <- local ctx (runDefinition x)
-- TODO: this feels hacky: for large types, we consider them "variables" that
-- have to be initialised, thus we re-bind them to variables within our context...
      let newCtx = addToCtx (map largeToVar defs) ctx
      rest <- foldDefs xs newCtx
      return (defs <> rest)

    largeToVar (s, (Type t)) = if isLarge t then (s, Type (MVar s)) else (s, (Type t))
    largeToVar x = x

    addToCtx [] ctx = ctx
    addToCtx ((str, val) : defs) ctx = 
      let newCtx = Context.insert str val ctx in
        addToCtx defs newCtx
  
eval (IHandle obj handler_list) = do
  handles <- mapM mkHandle handler_list
  pure $ Handler handles
  doHandle obj handles


eval (IHandleWith obj handler) = do
  handler <- eval handler 
  case handler of 
    (Handler action_list) -> doHandle obj action_list
    _ -> throwError "expected handle as right-hand argument in handle-with"
  

eval (IMkHandler handler_list) = do
  handles <- mapM mkHandle handler_list
  pure $ Handler handles

  
  
eval (IMatch term patterns) = do
  val <- eval term 
  ctx <- ask
  matched <- matchFirst val patterns 
  case matched of 
    Just (bindings, body) -> 
      let new_ctx =
            foldr (\(sym, val) ctx -> Context.insert sym val ctx)
                ctx bindings
        in
        local new_ctx (eval body)
    Nothing ->
      throwError "no pattern was matched"


  where
    matchFirst :: Expr -> [(IPattern, Intermediate)]
                 -> EvalM (Maybe ([(String, Expr)], Intermediate))
    matchFirst obj ((p, body) : patterns) = do
      result <- match obj p
      case result of 
        Just s -> pure $ Just (s, body)
        Nothing -> matchFirst obj patterns
    matchFirst _ [] = pure $ Nothing

    match :: Expr -> IPattern -> EvalM (Maybe [(String, Expr)])
    match (Constructor _ id1 id2 0 []) (ICheckPattern v sub_patterns) = do
      result <- eval v
      case result of 
        Constructor s id1' id2' _ _ -> 
          if (id1 == id1') && (id2 == id2') then
            pure $ Just []
          else
            pure Nothing
        _ -> throwError "(lit) patterns can only contain a constructor..."

    match (Variant _ id1 id2 lst) (ICheckPattern v sub_patterns) = do
      result <- eval v
      case result of 
        Constructor s id1' id2' nargs [] -> 
          if (id1 == id1') && (id2 == id2') && (nargs == length lst) then
            do 
              matched <- mapM (\(x, y) -> match x y) (zip lst sub_patterns)
              let 
                mflat (Just xs) (Just ys) = Just $ ys <> xs
                mflat _ _ = Nothing
              pure $ foldr mflat (Just []) matched
          else
            pure Nothing

        _ -> throwError "patterns can only contain a constructor..."

    match obj (ICheckPattern v sub_patterns) = do
      result <- eval v
      case result of 
        CustomCtor n _ _ d _ -> do
          ptn <- d obj
          case ptn of
            Just lst ->
              if n == length sub_patterns then
                do
                  matched <- mapM (\(x, y) -> match x y) (zip lst sub_patterns)
                  let 
                    mflat (Just xs) (Just ys) = Just $ ys <> xs
                    mflat _ _ = Nothing
                  pure $ foldr mflat (Just []) matched
  
              else
                throwError "length mismatch in pattern match"
            Nothing -> pure Nothing
        _ -> throwError "bad pattern-match"
        
    match x IWildCard = pure $ Just []
    match x (ISingPattern sym) = do
      ctx <- ask
      case (Context.lookup sym ctx, x) of 
        (Just (Constructor _ id1' id2' _ []), (Constructor _ id1 id2 0 [])) -> 
          if (id1 == id1') && (id2 == id2') then
            pure $ Just [] 
          else
            pure Nothing
        (Just (Constructor s id1' id2' nargs []), _) -> 
          pure Nothing
        (Just (CustomCtor 0 _ _ dtor _), _) -> do
          ptn <- dtor x
          case ptn of 
            Just [] -> pure (Just [])
            Nothing -> pure Nothing
        _ -> pure $ Just [(sym, x)]

    -- match _ _ _ = throwError "bad pattern-match"

    
eval (IDo xs) = evalToLast xs
  where evalToLast [] = throwError "do expecting at least one argument"
        evalToLast [x] = eval x
        evalToLast (x : xs) = 
          (eval x) >> (evalToLast xs)

  
  
eval (IDefinition _) =
  throwError ("definitions are currently implemented only in modules"
                  <> " and at the toplevel")

mkHandle :: (String, [String], Intermediate) -> EvalM (Int, Int, [String], Intermediate)
mkHandle (sym, syms, body) = 
  if sym == "val" then
    if length syms == 1 then
      pure (-1, -1, syms, body)
    else
      throwError "bad arguments to val-handler"
  else do
    ctx <- ask
    case Context.lookup sym ctx of
      Just (Action id1 id2 nargs []) -> 
        if (length syms - 1) == nargs then
          pure (id1, id2, syms, body)
        else
          throwError "bad nargs to handle-clause"
      _ -> throwError "expected action as handle-clause"

doHandle :: Intermediate -> [(Int, Int, [String], Intermediate)] -> EvalM Expr
doHandle obj handler_list = 
  let
    outerHandle :: MaybeEffect (ReaderT Context (ExceptT String (State ProgState))) Expr 
                -> ActionMonadT (ReaderT Context (ExceptT String (State ProgState))) Expr
    outerHandle obj =
      case obj of 
        (RaiseAction cnt id1 id2 args def) -> 
          let newCnt x =
                eval (IHandleWith
                      (IApply (IValue (liftFun cnt (MArr Undef Undef))) (IValue x))
                      (IValue (Handler handler_list))) in
          case findHandler id1 id2 handler_list of
            Just h ->
              let res = eval (unfoldArgs h (liftFun newCnt (MArr Undef Undef) : args)) in
                (feedEffect innerHandle) res 
            Nothing ->
              ActionMonadT (pure $ RaiseAction newCnt id1 id2 args def)
        (Value x) -> 
          case findHandler (-1) (-1) handler_list of 
            Just h ->
                let res = eval (IApply h (IValue x)) in
                (feedEffect innerHandle) res 
            Nothing -> pure x

    -- innerHandle :: MaybeEffect m Expr -> [(Int, Int, [String], Intermediate)] -> m Expr
    innerHandle obj =  
      case obj of 
        (RaiseAction cnt id1 id2 args def) -> 
          let newCnt x =
                eval (IHandleWith
                      (IApply (IValue (liftFun cnt (MArr Undef Undef))) (IValue x))
                      (IValue (Handler handler_list))) in
          case (findHandler id1 id2 handler_list) of 
            Just h ->
              let res = eval (unfoldArgs h (liftFun newCnt (MArr Undef Undef) : args)) in
              (feedEffect innerHandle) res 
            Nothing -> ActionMonadT (pure $ RaiseAction cnt id1 id2 args def)
        (Value x) -> pure x
      
    feedEffect :: Monad m => (MaybeEffect m a -> ActionMonadT m a) -> ActionMonadT m a -> ActionMonadT m a
    feedEffect f (ActionMonadT mnd) =
      let newf x = let (ActionMonadT mnd) = f x in mnd in
      ActionMonadT $ (mnd >>= newf)

    findHandler :: Int -> Int -> [(Int, Int, [String], Intermediate)] -> Maybe Intermediate
    findHandler id1 id2 [] = Nothing
    findHandler id1 id2 ((id1', id2', symList, body) : tl) 
      | id1 == id1' && id2 == id2' = Just (ILambda (map (\f -> (f, False)) (reAnn symList)) body)
      | otherwise = findHandler id1 id2 tl

    unfoldArgs :: Intermediate -> [Expr] -> Intermediate  
    unfoldArgs v [] = v
    unfoldArgs v (x : xs) = unfoldArgs (IApply v (IValue x)) xs
  in
    let res = eval obj in
      (feedEffect outerHandle) res

runDefinition :: IDefinition -> EvalM [(String, Expr)]
runDefinition val = do
  ctx <- ask
  case val of 
    ISingleDef str body ->  do
      result <- eval body 
      case result of 
        -- TODO: this is a hack around recursion...
        (Function args bdy fctx) -> 
          let newFunc = (Function args bdy newCtx)
              newCtx = Context.insert str newFunc fctx
          in
          return [(str, newFunc)]
        -- if is large type, we bound by name
        _ -> return $ [(str, result)]
    IVariantDef str _ body -> do
      val <- fresh_id
      let mkVariant :: (String, [Intermediate]) -> (Int, [(String, Expr)])
                    -> (Int, [(String, Expr)])
          mkVariant (s, i) (c, tl) = do
            ((c + 1), ((s, Constructor s val c (length i) []) : tl))

          (_, vars) = (foldr mkVariant (0, []) body)
      return $ vars
    IEffectDef str _ body -> do
      val <- fresh_id
      let mkEffect :: (String, [Intermediate]) -> (Int, [(String, Expr)])
                    -> (Int, [(String, Expr)])
          mkEffect (s, i) (c, tl) =
            ((c + 1), ((s, Action val c (length i - 1) []) : tl))

          (_, vars) = (foldr mkEffect (0, []) body)
      pure $ vars
    IOpenDef mod -> do
      mod <- eval mod 
      case mod of 
        (Module bindings) -> pure $ Map.toList bindings
        _ -> throwError "open requires module argument"






  
evalTopLevel :: Intermediate -> Context -> ProgState ->
    IO (Maybe (Either Expr [(String, Expr)], ProgState))
evalTopLevel expr ctx state =
  case expr of 
    -- Apply x [] -> evalTopLevel x ctx
    IDefinition def  -> do
      mdefs <- evalToIO (runDefinition def) ctx state
      case mdefs of 
        Just (mdefs, state') -> return $ Just (Right mdefs, state') 
        Nothing -> return Nothing
    _ -> do
      result <- evalToIO (eval expr) ctx state
      case result of 
        Just (val, state') -> return $ Just (Left val, state')
        Nothing -> return $ Nothing  

evalToIO :: EvalM a -> Context -> ProgState -> IO (Maybe (a, ProgState))
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
      putStrLn $ "error: " ++ err
      return Nothing
  where
    accumEffects :: EvalM Expr -> (Expr -> EvalM a) -> ProgState -> IO (Maybe (a, ProgState))
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
          putStrLn $ "error: " ++ err
          return Nothing


liftFun :: (Expr -> EvalM Expr) -> ModulusType -> Expr
liftFun f ty = InbuiltFun f ty

liftFun2 :: (Expr -> Expr -> EvalM Expr) -> ModulusType -> Expr
liftFun2 f ty = InbuiltFun (\x -> pure $ liftFun (f x) (getRetTy ty)) ty 

liftFun3 :: (Expr -> Expr -> Expr -> EvalM Expr) -> ModulusType -> Expr 
liftFun3 f ty = InbuiltFun (\x -> pure $ liftFun2 (f x) (getRetTy ty)) ty 

liftFun4 :: (Expr -> Expr -> Expr -> Expr -> EvalM Expr) -> ModulusType -> Expr 
liftFun4 f ty = InbuiltFun (\x -> pure $ liftFun3 (f x) (getRetTy ty)) ty 

getRetTy :: ModulusType -> ModulusType
getRetTy (MArr _ t) = t
getRetTy (MDep _ _ t) = t
getRetTy (ImplMDep _ _ t) = t
   


deAnn :: [Arg] -> [String]
deAnn ((Sym s) : ss) = s : (deAnn ss)
deAnn ((Annotation s _) : ss) = s : (deAnn ss)
deAnn [] = []
reAnn :: [String] -> [Arg]
reAnn (s : ss) = (Sym s) : (reAnn ss)
reAnn [] = []
