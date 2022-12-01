{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module Interpret.Eval (Normal,
                       Eval,
                       runEval,
                       eval,
                       evalTop,
                       evalDef,
                       runIO,
                       normSubst,
                       tyApp,
                       Result(..),
                       neu_equiv,
                       liftFun,
                       liftFun2,
                       liftFun3,
                       liftFun4,
                       liftFun5,
                       liftFun6,
                       liftFunL,
                       liftFunL2,
                       liftFunL3,
                       liftFunL4,
                       liftFunL5,
                       liftFunL6) where

import Prelude hiding (lookup)

import Data.Text (pack, unpack)
import Foreign.Ptr (FunPtr, Ptr)
import Foreign.LibFFI (Arg, callFFI,
                       argCInt, argCDouble, argString, argPtr,
                       retCDouble, retVoid, retCString)
import Foreign.C.String (peekCString)
import System.IO.Unsafe (unsafePerformIO)

import Control.Monad.State (State, MonadState, runState, runStateT)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.Reader (ReaderT, MonadReader, local, ask, runReaderT)
import qualified Interpret.Environment as Env

import Syntax.Utils  
import Interpret.EvalM (Eval, runEval)

import Bindings.Libtdl (CModule, lookupForeignFun, mkFun)
import Foreign.C.Types (CDouble)
  
import Syntax.Normal
import Syntax.Core
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vector

  
data Result m
  = RValue (Normal m)
  | RDef (Environment m -> Environment m)
  | RAnn String (Normal m)
  

loopThread :: IEThread Eval -> Environment Eval -> ProgState Eval -> IO (Either String (Normal Eval, ProgState Eval))
loopThread thread env state = 
  case thread of 
    IOThread io -> io >>= (\t -> loopThread t env state)
    MThread e -> case runEval e env state of
      Right (val, state') -> loopThread val env state'
      Left err -> pure $ Left err
    Seq l r -> case runEval l env state of
      Right (val, state') -> do
        res <- loopThread val env state'
        case res of
          Right (_, state') -> case runEval r env state of
            Right (val, state') -> loopThread val env state'
            Left err -> pure $ Left err
          Left err -> pure $ Left err
      Left err -> pure $ Left err
    Bind thread' fnc -> case runEval thread' env state of
      Right (thread'', state') -> do
          res <- loopThread thread'' env state'
          case res of 
            Right (val, state'') ->
              let mnd = do
                    fnc' <- fnc
                    res <- eval (CApp (CNorm fnc') (CNorm val))
                    case res of
                      (CollVal (IOAction action' ty')) -> pure action'
                      _ -> throwError ("io->>= expects result of called function to be IO monad, not: " <> show res)
              in case runEval mnd env state' of
                Right (val, state'') -> loopThread val env state'
                Left err -> pure $ Left err
            Left err -> pure $ Left err
      Left err -> pure $ Left err

    Pure val -> case runEval val env state of 
      Right (val', state') -> pure $ Right (val', state')
      Left err -> pure $ Left err


runIO :: Normal Eval -> Environment Eval -> ProgState Eval -> IO (Normal Eval, ProgState Eval)
runIO val env state =
  case val of
    (CollVal (IOAction action ty)) -> do
      res <- loopThread action env state
      case res of 
        Right val -> pure val
        Left err -> do
          putStrLn ("loopThread err: " <> err)
          pure (val, state)
    _ -> do
      print val
      pure (val, state)


evalTop :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => TopCore m -> m (Result m)
evalTop (TopExpr e) = eval e >>= (\val -> pure (RValue val))
evalTop (TopDef def) = case def of
  SingleDef name (CAbs sym core norm) ty -> do
    env <- ask
    let liftedFun = liftFun (\v -> local (const (Env.insert sym v ty liftedEnv)) (eval core)) norm
        liftedEnv = Env.insert name liftedFun norm env
    val <- local (const liftedEnv) (eval $ CAbs sym core norm)
    pure (RDef (Env.insert name val norm))

  SingleDef name body ty -> do
    val <- eval body
    pure (RDef (Env.insert name val ty))

  OpenDef body sig -> do
    mdle <- eval body
    case mdle of 
      NormSct m (NormSig ty) -> do
        let m' = (restrict . dropMod) (restrict (dropMod m) ty) sig
        pure $ RDef $ (flip $ foldr (\(k, (val, ty)) -> Env.insert k val ty)) m'
      _ -> throwError "cannot open non-module"

  InductDef sym indid params ctor ctorty alts -> do 
    let insertCtor = Env.insert sym ctor ctorty 
        insertAlts = flip (foldr (\(k, (val, ty)) env -> Env.insert k val ty env))

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          let alt = NormIVal sym indid id (length params) [] ty
          alts' <- mkAlts alts
          pure ((sym, (alt, ty)) : alts')
    alts' <- mkAlts alts
    pure $ RDef (insertCtor . insertAlts alts')

  CoinductDef sym coid params ctor ctorty alts -> do 
    let insertCtor = Env.insert sym ctor ctorty
        insertAlts = flip $ foldr (\(k, (val, ty)) -> Env.insert k val ty)

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          let alt = NormCoDtor sym coid id (tySize ty) (length params) [] ty
          alts' <- mkAlts alts
          pure ((sym, (alt, ty)) : alts')

    alts' <- mkAlts alts
    pure $ RDef (insertCtor . insertAlts alts')
evalTop (TopAnn sym term) = do
  term' <- eval term
  pure (RAnn sym term')


evalDef :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Definition m -> m [(String, (Normal m, Normal m))]
evalDef def = case def of
  SingleDef name (CAbs sym core norm) ty -> do
    env <- ask
    let liftedFun = liftFun (\v -> local (const $ Env.insert sym v ty liftedEnv) (eval core)) norm
        liftedEnv = Env.insert name liftedFun norm env
    val <- local (const $ liftedEnv) (eval $ CAbs sym core norm)
    pure [(name, (val, ty))]
  SingleDef name body ty -> do
    val <- eval body
    pure [(name, (val, ty))]
  OpenDef body sig -> do
    mdle <- eval body
    case mdle of 
      NormSct m (NormSig ty) -> 
        pure $ (restrict . dropMod) (restrict (dropMod m) ty) sig
      _ -> throwError "cannot open non-module"
  InductDef sym indid params ctor ctorty alts -> do 
    let ctorPr = (sym, (ctor, ctorty))

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          let alt = NormIVal sym indid id (length params) [] ty
          alts' <- mkAlts alts
          pure ((sym, (alt, ty)) : alts')
          
    
    alts' <- mkAlts alts
    pure $ (ctorPr : alts')
  CoinductDef sym coid params ctor ctorty alts -> do 
    let ctorPr = (sym, (ctor, ctorty))

        mkAlts [] = pure []
        mkAlts ((sym, id, ty) : alts) = do
          let alt = NormCoDtor sym coid id (tySize ty) (length params) [] ty
          alts' <- mkAlts alts
          pure ((sym, (alt, ty)) : alts')
    
    alts' <- mkAlts alts
    pure $ (ctorPr : alts')
  

-- evaluate an expression, to a normal form (not a value!). This means that the
-- environment now contains only normal forms!
eval :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Core m -> m (Normal m)
eval (CNorm n) = pure n

eval (CVar var) = do
  env <- ask
  fst <$> Env.lookup var env

eval (CArr l r) = do
  l' <- eval l
  r' <- eval r
  pure $ NormArr l' r'
  
eval (CProd var aty a b) = do
  a' <- eval a
  let ty = (NormUniv 0)
  b' <- local (Env.insert var (Neu (NeuVar var ty) ty) ty) (eval b)
  pure $ NormProd var aty a' b'

eval (CAbs var body ty) = do   
  hd <- tyHead ty
  body' <- local (Env.insert var (Neu (NeuVar var hd) hd) hd) (eval body)
  pure $ NormAbs var body' ty

eval (CApp l r) = do
  l' <- eval l
  apply l' r 


eval (CSct defs ty) = do
  defs' <- foldDefs defs -- TODO: add implicits to foldDefs
  pure $ NormSct defs' ty
  where
    --foldDefs :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [Definition m] -> m [(String, (Normal m, [Modifier]))]
    foldDefs [] = pure []
    foldDefs (def : defs) = do
      case def of  
        SingleDef var core ty -> do
          val <- eval core
          defs' <- local (Env.insert var val ty) (foldDefs defs)
          pure ((var, (val, [])) : defs')
        InductDef sym indid params ctor ctorty alts -> do
          let mkAlts [] = []
              mkAlts ((sym, id, ty) : alts) =
                let alt = NormIVal sym indid id (length params) [] ctor
                    alts' = mkAlts alts
                in ((sym, (alt, [])) : alts')
          pure ((sym, (ty, [])) : mkAlts alts)

eval (CSig defs) = do
  defs' <- foldDefs defs
  pure $ NormSig $ defs'
  where
    foldDefs :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [Definition m] -> m [(String, Normal m)]
    foldDefs [] = pure []
    foldDefs (def : defs) = do
      case def of
        SingleDef var core ty -> do
          val <- eval core
  -- TODO: is this really the solution? perhaps. 
          defs' <- local (Env.insert var (Neu (NeuVar var ty) ty) ty) (foldDefs defs)
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
    NormSct fields ty -> case getField field (dropMod fields) of 
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
          let update = flip (foldr (\(sym, (val, ty)) -> Env.insert sym val ty)) b
          local update (eval expr)
        Nothing -> match t as

    -- Take a value and a pattern. If the value matches the pattern, return a
    --   list of what variables to bind 
    --   otherwise, return none
    --getBinds :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Pattern m -> m (Maybe [(String, (Normal m, Normal m))])
    getBinds t WildCard = pure $ Just []
    getBinds t (VarBind sym ty) = pure $ Just [(sym, (t, ty))]
    getBinds (NormIVal _ id1 id2 strip params _) (MatchInduct id1' id2' patterns) = do
      if id1 == id1' && id2 == id2' then do
        nestedBinds <- mapM (uncurry getBinds) (zip (drop strip params) patterns)
        let allBinds = foldr (\b a -> case (a, b) of
                                (Just a', Just b') -> Just (a' <> b')
                                _ -> Nothing) (Just []) nestedBinds
        pure allBinds
      else pure Nothing
    getBinds n (InbuiltMatch fun) = fun n getBinds
    getBinds _ _ = pure Nothing

    -- construct a neutral matching term.
    --neuMatch :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Neutral m -> [(Pattern m, Core m)] -> m (Normal m)
    neuMatch n ps = do
      ps' <- mapM (\(pat, core) -> do
        norm <- local (getPatNeu pat) (eval core)
        pure (pat, norm)) ps
      pure $ Neu (NeuMatch n ps' ty) ty

    getPatNeu :: Pattern m -> Environment m -> Environment m
    getPatNeu WildCard = id
    getPatNeu (VarBind sym ty) = Env.insert sym (Neu (NeuVar sym ty) ty) ty 
    getPatNeu (MatchInduct id1 id2 pats) = flip (foldr getPatNeu) pats 

eval (CCoMatch patterns ty) =
  pure $ NormCoVal (map evalCoPat patterns) ty
  where
    evalCoPat :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (CoPattern m, Core m) -> (CoPattern m, m (Normal m))
    evalCoPat (pat, body) = (pat, (local (getPatNeu pat) (eval body)))

    getPatNeu :: CoPattern m -> Environment m -> Environment m
    getPatNeu CoWildCard = id
    getPatNeu (CoVarBind sym ty) = Env.insert sym (Neu (NeuVar sym ty) ty) ty
    getPatNeu (CoMatchInduct _ _ _ pats) = flip (foldr getPatNeu) pats

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

eval (CAdaptForeign lang libsym imports) = do
  case lang of 
    "c" -> do
      lib <- eval $ CVar libsym
      case lib of
        NormCModule m -> do
          vals <- mapM (\(_, fsym, ty) -> getAsBuiltin m fsym ty) imports
          let ty = NormSig $ map (\(s, _, ty) -> (s, ty)) imports
          pure $ NormSct (toEmpty $ zipWith (\(s, _, ty) val -> (s, val)) imports vals) ty
        _ -> throwError "foreign-adapter only works if module is available at compile?-time!"
    _ -> throwError "can only load c modules"

eval other = throwError ("eval not implemented for" <> show other)


normSubst ::  (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m, String) -> Normal m -> m (Normal m)
normSubst (val, var) ty = case ty of 
  Neu neu ty -> neuSubst (val, var) neu
  PrimType p -> pure $ PrimType p
  PrimVal p -> pure $ PrimVal p
  Refl ty -> Refl <$> normSubst (val, var) ty
  PropEq lty rty -> PropEq <$> normSubst (val, var) lty <*> normSubst (val, var) rty

  CollTy cty -> case cty of 
    MaybeTy a -> (CollTy . MaybeTy) <$> normSubst (val, var) a
    ListTy a -> (CollTy . ListTy) <$> normSubst (val, var) a
    ArrayTy a -> CollTy <$> (ArrayTy <$> normSubst (val, var) a)
    IOMonadTy a -> (CollTy . IOMonadTy) <$> normSubst (val, var) a
    CPtrTy a -> (CollTy . CPtrTy) <$> normSubst (val, var) a

  CollVal cvl -> case cvl of 
    MaybeVal m ty -> case m of 
      Just some -> CollVal <$> (MaybeVal <$> (Just <$> (normSubst (val, var) some))
                                <*> normSubst (val, var) ty)
      Nothing -> CollVal <$> (MaybeVal Nothing <$> normSubst (val, var) ty)
    ListVal vals ty -> CollVal <$> (ListVal <$> mapM (normSubst (val, var)) vals <*> normSubst (val, var) ty)
    ArrayVal vec ty -> CollVal <$> (ArrayVal <$> Vector.mapM (normSubst (val, var)) vec
                                    <*> normSubst (val, var) ty)
    IOAction thread ty -> do
      ty' <- normSubst (val, var) ty  
      let thread' = threadSubst thread 
      pure . CollVal $ IOAction thread' ty'

      where
        -- TODO: seems dodgy (shoudl we substitue into result of IO??)
        threadSubst (IOThread t) = (IOThread t)
        threadSubst (MThread t)  = (MThread t)
        threadSubst (Seq l r)    = Seq (threadSubst <$> l) (threadSubst <$> r)
        threadSubst (Bind v f)   = Bind (threadSubst <$> v) (f >>= normSubst (val, var))
        threadSubst (Pure v)     = Pure (v >>= normSubst (val, var))

  NormCoVal pats ty -> do
    let pats' = map substCoPat pats
    ty' <- normSubst (val, var) ty
    pure (NormCoVal pats' ty')
    where 
      --substCoPat :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (CoPattern m, m (Normal m)) -> (CoPattern m, m (Normal m))
      substCoPat (copattern, body) = do
        let vars = getCoPatVars copattern in
          if Set.member var vars then
            (copattern, body)
          else
            (copattern, (body >>= normSubst (val, var)))

      --getCoPatVars :: CoPattern m -> Set.Set String
      getCoPatVars CoWildCard = Set.empty
      getCoPatVars (CoVarBind var _) = Set.singleton var
      getCoPatVars (CoMatchInduct _ _ _ subPatterns) =
        foldr (Set.union . getCoPatVars) Set.empty subPatterns
 
  NormUniv n -> pure $ NormUniv n
  
  NormProd var' aty a b ->
    if var == var' then  do
      a' <- normSubst (val, var) a
      pure $ NormProd var' aty a' b
    else do
      a' <- normSubst (val, var) a
      b' <- normSubst (val, var) b
      pure $ NormProd var' aty a' b'

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

  -- TODO: The function /may/ have captured variables in it as a closure?
  -- pretty sure this shouldn't happen as we have InbuiltNeuApp
  Builtin fnc ty -> do
    Builtin fnc <$> normSubst (val, var) ty
  BuiltinLzy fnc ty -> do
    BuiltinLzy fnc <$> normSubst (val, var) ty


  NormSct fields ty -> do
    let (fields', mods) = peelMod fields
    fields'' <- substFields (val, var) fields'
    NormSct (addMod fields'' mods) <$> normSubst (val, var) ty

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
    substFields :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m, String) -> [(String, Normal m)] -> m [(String, Normal m)]
    substFields (val, var) ((var', val') : fields) = do
      if var == var' then 
        pure $ (var', val') : fields
      else do
        val'' <- normSubst (val, var) val'
        fields' <- substFields (val, var) fields 
        pure $ (var', val'') : fields'
    substFields (val, var) [] = pure []

  
neuSubst :: (MonadReader (Environment m) m, MonadState (ProgState m) m , MonadError String m) => (Normal m, String) -> Neutral m -> m (Normal m)
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
      NormAbs var body ty -> do 
        normSubst (r', var) body
      Builtin fn ty -> fn r'
      v -> throwError ("bad app to:" <> show v <> ", attempted to apply: " <> show r')

  NeuDot n field -> do
    mdle <- neuSubst (val, var) n
    case mdle of 
      Neu n ty -> do
        ty' <- tyField field ty
        pure $ Neu (NeuDot n field) ty'
  -- TODO: restrict by ty
      NormSct fields ty ->
        case (getField field (dropMod fields)) of
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
       --match :: (MonadReader Environment m, MonadError String m, MonadState ProgState m) => Normal -> [(Pattern, Normal)] -> m Normal
       match t [] = throwError ("couldn't match value: " <> show t)
       match t ((pat, expr) : as) =
         case getBinds t pat of
           Just b -> do
             expr' <- foldBinds b expr
             normSubst (val, var) expr'
             where
               foldBinds ((var, val) : bs) expr = normSubst (val, var) expr >>= foldBinds bs
               foldBinds [] expr = pure expr
           Nothing -> match t as
    
       getBinds :: Normal m -> Pattern m -> Maybe [(String, Normal m)]
       getBinds t WildCard = Just []
       getBinds t (VarBind sym _) = Just [(sym, t)]
       getBinds (NormIVal _ id1 id2 strip params _) (MatchInduct id1' id2' patterns) =
         if id1 == id1' && id2 == id2' then 
           let nestedBinds = map (uncurry getBinds) (zip (drop strip params) patterns)
               allBinds = foldr (\b a -> case (a, b) of
                                   (Just a', Just b') -> Just (a' <> b')
                                   _ -> Nothing) (Just []) nestedBinds
               in allBinds
         else Nothing
       getBinds _ _= Nothing


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
tyField :: (MonadError String m) => String -> Normal m -> m (Normal m)  
tyField field (NormSig fields) =
  case getField field fields of
    Just x -> pure x
    Nothing -> throwError ("can't find field: " <> field)
tyField field (NormSct fields _) =
  case getField field (dropMod fields) of
    Just x -> pure x
    Nothing -> throwError ("can't find field: " <> field)
tyField field term = throwError ("can't get field  " <> field <> " of non struct/sig: " <> show term)

tyApp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> m (Normal m)
tyApp (NormArr l r) _ = pure r 
tyApp (NormProd sym _ a b) arg = normSubst (arg, sym) b



instance Eq (Normal m) where
  a == b = norm_equiv a b (Set.empty, 0) (Map.empty, Map.empty)


-- TODO: add eta reductions to the equality check
norm_equiv :: Normal m -> Normal m -> Generator -> (Map.Map String String, Map.Map String String) -> Bool 
norm_equiv (NormUniv n1) (NormUniv n2) gen rename = n1 == n2
norm_equiv (Neu n1 _) (Neu n2 _) gen rename = neu_equiv n1 n2 gen rename
norm_equiv (PrimVal p1)  (PrimVal p2) _ _  = p1 == p2
norm_equiv (PrimType p1) (PrimType p2) _ _ = p1 == p2
norm_equiv (Special s1)  (Special s2) _ _  = s1 == s2
norm_equiv (Keyword s1)  (Keyword s2) _ _  = s1 == s2
norm_equiv (Symbol s1)   (Symbol s2) _ _   = s1 == s2

-- Note: arrows and dependent types /can/ be equivalent if the bound variable
-- doesn't come on the LHS
norm_equiv (NormProd var aty1 a b) (NormProd var' aty2 a' b') gen (lrename, rrename) = 
  let (nvar, gen') = genFresh gen
  in (a == a')
    && (aty1 == aty2)
    && (norm_equiv b b'
        (useVars [var, var', nvar] gen')
        (Map.insert var nvar lrename, Map.insert var' nvar rrename))
norm_equiv (NormArr a b)     (NormArr a' b') gen rename = 
  (norm_equiv a a' gen rename) || (norm_equiv b b' gen rename)
norm_equiv (NormProd var Visible a b) (NormArr a' b') gen rename = 
  if Set.member var (free b) then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename
norm_equiv (NormArr  a b) (NormProd var' Visible a' b') gen rename = 
  if Set.member var' (free b') then
    False
  else
    norm_equiv a a' gen rename && norm_equiv b b' gen rename

norm_equiv (CollTy x) (CollTy y) gen rename =
  case (x, y) of 
    (MaybeTy a, MaybeTy b) -> norm_equiv a b gen rename

norm_equiv (CollVal x) (CollVal y) gen rename =
  case (x, y) of 
    (MaybeVal (Just a) t1, MaybeVal (Just b) t2) ->
      (norm_equiv a b gen rename) && (norm_equiv t1 t2 gen rename)
    (MaybeVal Nothing t1, MaybeVal Nothing t2) ->
      (norm_equiv t1 t2 gen rename)
    (MaybeVal _ _, MaybeVal _ _) -> False

-- norm_equiv (NormSig fields1) (NormSig fields1) = 
--   case (x, y)

-- norm_equiv (NormSct fields1 ty1) (NormSct fields1 ty2)
  
norm_equiv _ _ _ _ = False

  
neu_equiv :: Neutral m -> Neutral m -> Generator -> (Map.Map String String, Map.Map String String)
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


-- runEvalT :: Monad m => EvalM m a -> Environment -> ProgState -> m (Either String (a, ProgState))
-- runEvalT inner_mnd ctx state =
--   fmap unwrap (runStateT (runExceptT (runReaderT inner_mnd ctx)) state)
--   where
--     unwrap (Right obj, state') = Right (obj, state')
--     unwrap (Left err, state')  = Left $ "err: " <> err


applyDtor :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Int -> Int -> Int -> [Normal m] -> m (Normal m)
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


getAsBuiltin :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => CModule -> String -> Normal m -> m (Normal m)
getAsBuiltin m sym ty =
  case lookupForeignFun m sym of
    Just f ->
      if isFncType ty then do
        let retTy = getRet ty
            lst = argList ty
        ty' <- tyTail ty
        pure $ liftFun (cCall f lst [] retTy ty') ty
      else doCall ty f []
    _ -> throwError ("cannot currently interpret as foreign c type " <> show ty)

  where 
    argList (NormArr l r) = l : argList r
    argList (NormProd sym _ a b) = a : argList b
    argList _ = []

    --cCall :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => FunPtr () -> [Normal m] -> [Arg m] -> Normal m -> Normal m -> Normal m -> m (Normal m)
    cCall fnc [argTy] cargs retTy ty' arg = do
      carg <- getArg argTy arg
      doCall retTy fnc (carg:cargs)
    cCall fnc (argty:args) cargs retTy ty' val = do
      carg <- getArg argty val
      ty'' <- tyTail ty'
      pure $ liftFun (cCall fnc args (carg:cargs) retTy ty'') ty'

    doCall retTy fnc cargs = 
      case retTy of 
        (PrimType CDoubleT) ->
          pure . PrimVal . CDouble $ unsafePerformIO $ callFFI fnc retCDouble cargs

        (CollTy (IOMonadTy ty)) -> case ty of 
          (PrimType UnitT) -> 
            pure . CollVal $ IOAction
              (IOThread (callFFI fnc retVoid cargs >> (pure (Pure (pure (PrimVal Unit))))))
              (CollTy (IOMonadTy (PrimType UnitT)))
        _ -> throwError ("bad cffi ret ty: " <> show retTy)

  

    getArg (PrimType CDoubleT) (PrimVal (CDouble d)) =  
      pure $ argCDouble d
    getArg (PrimType CIntT) (PrimVal (CInt i)) =  
      pure $ argCInt i 
    getArg (PrimType CStringT) (PrimVal (CString s)) =  
      pure $ argString (unsafePerformIO $ peekCString s) -- TODO: fix CStrings!!
    getArg (CollTy (CPtrTy _)) (CollVal (CPtr val)) = 
      pure $ argPtr val -- TODO: fix CStrings!!
    getArg ty val = throwError ("bad getArg in getAsBuiltin: " <> show ty <> "," <> show val)

    getRet (NormArr _ r) = getRet r
    getRet (NormProd _ _ _ r) = getRet r
    getRet v = v



apply :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Core m -> m (Normal m) 
apply (Neu neu ty) r = do
  -- TODO: thunk about thunks and neutral terms...
  -- thunk <- genThunk r
  r' <- eval r
  ty' <- tyApp ty r'
  pure $ Neu (NeuApp neu r') ty'
apply (NormAbs var body ty) r = do
  r' <- eval r
  normSubst (r', var) body
apply (Builtin fn ty) r = eval r >>= fn
apply (BuiltinLzy fn ty) r = fn (eval r)
apply (NormIVal name tyid altid strip params ty) r = do
  r' <- eval r
  ty' <- tyApp ty r'
  pure $ NormIVal name tyid altid strip (r' : params) ty'
apply (NormCoDtor name id1 id2 len strip args ty) r = do
  r' <- eval r
  ty' <- tyApp ty r'
  case len of
    0 -> throwError "too many arugments to destructor"
    1 -> applyDtor id1 id2 strip (reverse (r' : args))
    _ -> pure $ NormCoDtor name id1 id2 (len - 1) strip (r' : args) ty
apply (InbuiltCtor ctor) r = case ctor of
  IndPat _ _ _ n _ -> do
    r' <- eval r
    eval (CApp (CNorm n) (CNorm r'))
apply other _ = throwError ("tried to apply to non-function: " <> show other)

-- eventual evaluation of non-strict application
-- eval (CApp l r rty) = do
--   l' <- eval l
--   case l' of 
--     Neu neu ty -> do
--       ty' <- tyAppThunk ty thunk ??
--       pure $ Neu (NeuApp neu thunk) ty'
--     NormAbs var lzy body ty ->
--       if lzy then do
--         thunk <- genThunk r
--         normSubstT (thunk, var) body
--       else do
--         val <- eval r'
--         normSubst (val, var) body
--     Builtin fn ty -> fn (eval r) -- builtin functions will handle strictness
--                                  -- internally if they need to 
--     NormIVal name tyid altid strip params lzys ty -> do
--       case safeHead lzys of 
--         Just True
--         Just False
--         Nothing -> throwError ("too many args to Normal: " <> name)
--       r' <- eval r 
--       ty' <- tyApp ty r'
--       pure $ NormIVal name tyid altid strip (r' : params) ty'
--     NormCoDtor name id1 id2 len strip args ty -> do
--       r' <- eval r 
--       ty' <- tyApp ty r'
--       case len of 
--         0 -> throwError "too many arugments to destructor"
--         1 -> applyDtor id1 id2 strip (reverse (r' : args))
--         _ -> pure $ NormCoDtor name id1 id2 (len - 1) strip (r' : args) ty
--     InbuiltCtor ctor -> case ctor of   
--       r' <- eval r 
--       IndPat _ _ _ n _ -> eval (CApp (CNorm n) (CNorm r'))
--     other -> throwError ("tried to apply to non-function: " <> show other)


applyNorm :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> Normal m -> m (Normal m) 
applyNorm (Neu neu ty) r' = do
  ty' <- tyApp ty r'
  pure $ Neu (NeuApp neu r') ty'
applyNorm (NormAbs var body ty) r' = normSubst (r', var) body
applyNorm (Builtin fn ty) r' = fn r'
applyNorm (NormIVal name tyid altid strip params ty) r' = do
  ty' <- tyApp ty r'
  pure $ NormIVal name tyid altid strip (r' : params) ty'
applyNorm (NormCoDtor name id1 id2 len strip args ty) r' = do
  ty' <- tyApp ty r'
  case len of
    0 -> throwError "too many arugments to destructor"
    1 -> applyDtor id1 id2 strip (reverse (r' : args))
    _ -> pure $ NormCoDtor name id1 id2 (len - 1) strip (r' : args) ty
applyNorm (InbuiltCtor ctor) r' = case ctor of
  IndPat _ _ _ n _ -> eval (CApp (CNorm n) (CNorm r'))
applyNorm other _ = throwError ("tried to apply to non-function: " <> show other)



---- FUNCTION LIFTING  
-- Utilities for lifting Haskell functions on Modulus objects into a Modulus Function.
  
interceptNeutral :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m -> m (Normal m)) -> Normal m -> Normal m -> m (Normal m)
interceptNeutral f ty (Neu neutral nty) = do
  ty' <- tyApp ty nty
  pure $ Neu (NeuBuiltinApp (interceptNeutral f ty) neutral ty') ty'
interceptNeutral f ty val = f val


-- liftFun needs to intercept /neutral/ terms!
liftFun :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m -> m (Normal m)) -> Normal m -> Normal m
liftFun f ty = Builtin (interceptNeutral f ty) ty


liftFun2 :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m -> Normal m -> m (Normal m)) -> Normal m -> Normal m
liftFun2 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ ->
                  case ty of
                    (NormArr _ r) -> pure $ liftFun (f val) r
                    (NormProd var _ _ body) -> pure $ liftFun (f val) body
  in Builtin f' ty


liftFun3 :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m -> Normal m -> Normal m -> m (Normal m)) -> Normal m -> Normal m
liftFun3 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun2 (f val) r
                  (NormProd var _ _ body) -> pure $ liftFun2 (f val) body
  in Builtin f' ty


liftFun4 :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)) -> Normal m -> Normal m
liftFun4 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun3 (f val) r
                  (NormProd var _ _ body) -> pure $ liftFun3 (f val) body
  in Builtin f' ty


liftFun5 :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)) -> Normal m -> Normal m
liftFun5 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun4 (f val) r
                  (NormProd var _ _ body) -> pure $ liftFun4 (f val) body
    in Builtin f' ty


liftFun6 :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)) -> Normal m -> Normal m
liftFun6 f ty =
  let f' val = case val of
                (Neu neu nty) -> do
                  ty' <- tyApp ty nty
                  pure $ Neu (NeuBuiltinApp f' neu ty') ty'
                _ -> case ty of
                  (NormArr _ r) -> pure $ liftFun5 (f val) r
                  (NormProd var _ _ body) -> pure $ liftFun5 (f val) body
    in Builtin f' ty


-- Lazy Function Lifting
  
-- interceptNeutral :: (EvalM Normal -> EvalM Normal) -> Normal -> Normal -> EvalM Normal
-- interceptNeutral f ty (Neu neutral nty) = do
--   ty' <- tyApp ty nty
--   pure $ Neu (NeuBuiltinApp (interceptNeutral f ty) neutral ty') ty'
-- interceptNeutral f ty val = f val

liftFunL :: (m (Normal m) -> m (Normal m)) -> Normal m -> Normal m
liftFunL f ty = BuiltinLzy f ty


liftFunL2 :: Applicative m => (m (Normal m) -> m (Normal m) -> m (Normal m)) -> Normal m -> Normal m
liftFunL2 f ty =
  let f' val = case ty of
        (NormArr _ r) -> pure $ liftFunL (f val) r
        (NormProd var _ _ body) -> pure $ liftFunL (f val) body
  in BuiltinLzy f' ty


liftFunL3 :: Applicative m => (m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m)) -> Normal m -> Normal m
liftFunL3 f ty =
  let f' val = case ty of
        (NormArr _ r) -> pure $ liftFunL2 (f val) r
        (NormProd var _ _ body) -> pure $ liftFunL2 (f val) body
  in BuiltinLzy f' ty


liftFunL4 :: Applicative m => (m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m)) -> Normal m -> Normal m
liftFunL4 f ty =
  let f' val = case ty of
        (NormArr _ r) -> pure $ liftFunL3 (f val) r
        (NormProd var _ _ body) -> pure $ liftFunL3 (f val) body
  in BuiltinLzy f' ty


liftFunL5 :: Applicative m => (m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m)) -> Normal m -> Normal m
liftFunL5 f ty =
  let f' val = case ty of
        (NormArr _ r) -> pure $ liftFunL4 (f val) r
        (NormProd var _ _ body) -> pure $ liftFunL4 (f val) body
  in BuiltinLzy f' ty


liftFunL6 :: Applicative m => (m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m) -> m (Normal m)) -> Normal m -> Normal m
liftFunL6 f ty =
  let f' val = case ty of
        (NormArr _ r) -> pure $ liftFunL5 (f val) r
        (NormProd var _ _ body) -> pure $ liftFunL5 (f val) body
  in BuiltinLzy f' ty
