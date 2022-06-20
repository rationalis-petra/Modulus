module Typecheck.Typecheck where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.State (State, get, modify, put, runState)
import Control.Monad.Except (Except, ExceptT,
                             lift, runExcept, runExceptT, throwError, catchError) 

import Data (Object(Type, Module),
             PrimE(..),
             ModulusType(..),
             PrimType(..))
import Data.Environments
import qualified Typecheck.Environment as Env
import Syntax.TIntermediate  

import Typecheck.TypeUtils  

type SigMap = Map.Map String ModulusType
type TI = ExceptT String (State (Map.Map Int ModulusType, Int))

  

runChecker :: TIntermediate -> CheckEnv -> Either String (TIntermediate, ModulusType)
runChecker int env =
  let mnd = do
        (i, e) <- typeCheck int env
        t <- envToModulus e env
        pure (i, t)
  in
  case runState (runExceptT mnd) (Map.empty, 0) of 
    (Left err, _) -> Left err
    (Right val, _) -> Right val

  
runCheckerTop :: TIntTop -> CheckEnv -> Either String (Either (TIntTop, ModulusType) TIntTop)
runCheckerTop top env =
  let mnd = do
        res <- typeCheckTop top env
        case res of
          Left (i, e) -> do
            t <- envToModulus e env
            pure (Left (i, t))
          Right e -> pure (Right e)
  in
  case runState (runExceptT mnd) (Map.empty, 0) of 
    (Left err, _) -> Left err
    (Right val, _) -> Right val

typeCheckTop :: TIntTop -> CheckEnv -> TI (Either (TIntTop, EnvVal) TIntTop)
typeCheckTop (TExpr e) env = (Left . (\(x, y) -> (TExpr x, y))) <$> typeCheck e env
typeCheckTop (TDefinition def) env = 
  case def of 
    TSingleDef name expr Nothing -> do
      (expr', ty) <- typeCheck expr env
      mty <- envToModulus ty env
      pure $ Right $ TDefinition $ TSingleDef name expr' (Just mty)

    TSingleDef name expr (Just mty) -> do
      (expr', ty) <- typeCheck expr env
      mty' <- envToModulus ty env
      checkEq mty mty'
      pure $ Right $ TDefinition $ TSingleDef name expr' (Just mty)

    TOpenDef expr Nothing -> do 
      (expr', ty) <- typeCheck expr env
      mty <- envToModulus ty env
      pure $ Right $ TDefinition $ TOpenDef expr' (Just mty)

    TVariantDef nme params id alrs ty -> 
      -- TODO: check for well-formedness!! (maybe?)
      pure $ Right $ TDefinition $ TVariantDef nme params id alrs ty
    -- TEffectDef  String [String] Int [(String, Int, [ModulusType])]
  


-- Typecheck
-- The typecheck function takes a typed intermediate and a type environment,
-- returning a new typed intermediate and EnvVal (which can be reduced to a type
-- in a given environment). The new intermediate will be different form the
-- original in that
-- + All functions will be annotated
-- + All implicit arguments are instantiated
-- This means it can then be translated into a value in Core, where neither
-- inference nor implicit arguments are allowed. 
typeCheck :: TIntermediate -> CheckEnv -> TI (TIntermediate, EnvVal)

-- Typecheck a value: all values (of Object type) either carry their type with
-- them or it is easily deducible.  
typeCheck (TValue expr) env = do
  case runExcept (typeExpr expr) of 
    Right t -> pure (TValue expr, Var t)
    Left err -> throwError err

-- Typecheck a symbol: simply lookup the symbol within our type environment. 
typeCheck (TSymbol s) env = do
  case runExcept (Env.lookup s env) of 
    Right x -> pure (TSymbol s, x)
    Left err -> throwError ("couldn't find type of " <> s <> " when typechecking")

typeCheck (TAccess int s) env = do
  (newInt, newt) <- typeCheck int env
  newt' <- envToModulus newt env 
  case newt' of 
    Signature m -> case Map.lookup s m of
      Just t -> pure (TAccess newInt s, Var t)
      Nothing -> throwError ("field " <> s <> " missing from signature " <> show newt')
    _ -> throwError ("expected access of field " <> s <> " to be signature, but was " <> show newt')

-- Typecheck an application: we need to
-- 1. Check the type of the /argument/ 
-- 2. Pass it in as a constraint to a subroutine (for inferring implicit arguments)
-- 4. If is regular function, just check arg against type of i2.
typeCheck (TApply i1 i2) env = do 
  (i2', targ) <- typeCheck i2 env
  mls <- envToModulus targ env
  applyInfer i1 [mls] env
  (i1', tfun) <- applyInfer i1 [mls] env
  m <- envToModulus tfun env
  case m of
    MArr arg result -> do
      i2'' <- update targ i2' (Var arg)
      pure (TApply i1' i2'', Var result)
     `catchError` (\msg -> throwError (msg <> ", mls = " <> show mls))
    MDep arg s result -> do  
      i2'' <- update targ i2' (Var arg)
      res <- depType i2''
      pure (TApply i1' i2'', Var  (subst s res result))
     `catchError` (\msg -> throwError (msg <> ", mls = " <> show mls))
    t -> 
      throwError ("bad TApply lhs type, got: " <> show t <> " rhs " <> show mls)

  where
    applyInfer :: TIntermediate -> [ModulusType] -> CheckEnv -> TI (TIntermediate, EnvVal)
    applyInfer (TApply i1 i2) constraints env = do 
      (i2', targ) <- typeCheck i2 env
      -- TODO: (possbug) maybe unfiy the arguments with types or smth first?? not sure tho...
      mls <- envToModulus targ env
      (i1', tfun) <- applyInfer i1 (mls : constraints) env
      f <- envToModulus tfun env
      case f of 
        MArr arg result -> do
          i2'' <- update targ i2' (Var arg)
          pure (TApply i1' i2', Var result)
        MDep arg s result -> do  
          i2'' <- update targ i2' (Var arg)
          -- the value of the argument must be available at checking-Time!
          res <- depType i2''
          pure (TApply i1' i2'', Var (subst s res result))
        t ->
          throwError ("bad TApply lhs type, got: " <> show t <> " with " <> show mls)
    applyInfer base constraints env = do
      (fnc, tfun) <- typeCheck base env
      f <- envToModulus tfun env
      case f of 
        ImplMDep (TypeN 1) s a ->
          case deduceType s a constraints of 
            Just inferredType -> do
              applyInfer (TImplApply fnc (TValue (Type inferredType))) constraints env
            Nothing -> throwError ("implicit type argument resolution failed!")
        ImplMDep (Signature map) s a -> do
          mlde <- deduceModule map s a constraints env
          applyInfer (TImplApply fnc mlde) constraints env
        _ -> pure (fnc, tfun)
      
-- Typechecking implicit application:
-- With implicit application, we don't need to worry about whether to deduce an
-- arg: it is assumed to be the "leftmost" argument :) 
typeCheck (TImplApply i1 i2) env = do 
  (i2', targ) <- typeCheck i2 env
  (i1', tfun) <- typeCheck i1 env
  tfun' <- envToModulus tfun env
  case tfun' of 
    ImplMDep t s r -> do
      i1'' <- update targ i1' (Var t)
      res <- depType i2'
      pure (TImplApply i1' i2', Var (subst s res r))
    t -> throwError ("bad lhs in TImplApply: " <> show t)


-- Typechecking a function:
-- 1. For each argument, add ti to the environment, either with a type (if
--    annotated) or as a type-variable for unification.
-- 2. Check the body of the function
-- 3. If any types were annotated, add type-variables as implicit
--    arguments. Otherwise, Just return
typeCheck (TLambda args body _) env = do
  (args', body', t, free) <- processArgs args env
  mls <- envToModulus t env
  let (args'', t') = addImplicits (Set.toList free) args' mls
  mty <- envToModulus t' env
  pure (TLambda args'' body' (Just mty), t')
  where 
    processArgs :: [(TArg, Bool)] -> CheckEnv
                -> TI ([(TArg, Bool)], TIntermediate, EnvVal, Set.Set String)
    processArgs [] env = do
      (i, t) <- typeCheck body env 
      pure ([], i, t, Set.empty)
    processArgs ((x, b):xs) env = case x of 
      BoundArg s t -> do
        (a, i, e, f) <- processArgs xs (Env.insert s (Var t) env)
        t' <- envToModulus e env
        if b then
          pure (((x, b) : a), i, Var (ImplMDep t s t'), f)
        else
          pure (((x, b) : a), i, Var (MDep t s t'), f)
      ValArg s t -> do
        (a, i, e, f) <- processArgs xs (Env.insert s (Var t) env)
        t' <- envToModulus e env
        if b then
          throwError "regular args cannot be implicit: only dependent (bound) ones"
        else
          pure (((x, b) : a), i, Var (MArr t t'), f)
      InfArg s -> do
        t <- newT
        (a, i, e, f) <- processArgs xs (Env.insert s t env)
        r <- envToModulus e env
        l <- envToModulus t env
        let impls = (getFree r Set.empty)
        pure (((ValArg s l, False) : a), i, Var (MArr l r), impls <> f)

    addImplicits :: [String] -> [(TArg, Bool)] -> ModulusType
                 -> ([(TArg, Bool)], EnvVal)
    addImplicits impls as t =
      let fst = map (\s -> (BoundArg s (TypeN 1), True)) impls <> as
          snd = Var (constructTop impls)
          constructTop [] = t
          constructTop (s : ss) = ImplMDep (TypeN 1) s (constructTop ss)
      in (fst, snd)

typeCheck (TModule defs) env = do
  -- TODO: recursion! 
  (defs', types) <- checkModule defs env 
  types' <- mapM (\(l, r) -> (envToModulus r env) >>= (\f -> pure (l, f))) types
  pure (TModule defs', Var $ Signature $ Map.fromList types')
     
  where
    checkModule :: [TDefinition] -> CheckEnv -> TI ([TDefinition], [(String, EnvVal)])
    checkModule [] env = pure ([], [])
    checkModule ((TSingleDef s i Nothing) : ds) env = do
      (i', ty) <- typeCheck i env
      mty <- envToModulus ty env
      (ds', ts) <- checkModule ds (Env.insert s ty env)
      pure (TSingleDef s i' (Just mty) : ds', (s, ty) : ts)
    checkModule ((TVariantDef nme params id defs ty) : ds) env = do
      -- TODO: check for well-formedness
      -- Question: has this already been done by the earlier toTIntermediate
      -- function?
      let vtype' [] = ty
          vtype' (s : ss) = MDep (TypeN 1) s (vtype' ss)
          vtype = vtype' params
          
          getVars [] = []
          getVars ((s, _, ts) : vs) =
            (s, mkFunType ts vtype) : getVars vs

          mkFunType [] b = b
          mkFunType (t : ts) b = MArr t (mkFunType ts b)
            
          vars = getVars defs
          vars' = map (\(s, t) -> (s, Var t)) ((nme, vtype) : vars)
      (ds', ts) <- checkModule ds (foldr (\(s, t) -> Env.insert s t) env vars')
      pure ((TVariantDef nme params id defs ty) : ds, (vars' <> ts))
    checkModule _ env = throwError "typecheck not done all defs!" 
  
typeCheck (TSignature defs) env = do
  -- TODO: check for well-formedness 
  pure (TSignature defs, Var $ Large)

typeCheck (TIF cond e1 e2) env = do
  (cond', cnd)  <- typeCheck cond env
  cond'' <- update cnd cond' (Var (MPrim BoolT))
  (e1', t1)  <- typeCheck e1 env
  (e2', t2)  <- typeCheck e2 env
  e2''  <- update t1 e2' t2
  pure ((TIF cond'' e1' e2''), t2)

typeCheck (TMatch expr patterns) env = do
  (expr', texpr) <- typeCheck expr env
  (patterns', tbody, texpr') <- checkMatches patterns texpr 
  expr' <- update texpr expr texpr'
  pure (TMatch expr' patterns', tbody)
  where
    -- assume list is non-empty: todo/check to make sure non-empty throws error
    checkMatches :: [(TPattern, TIntermediate)] -> EnvVal
                 -> TI ([(TPattern, TIntermediate)], EnvVal, EnvVal)
    checkMatches [(p, body)] texpr = do
      -- check the pattern
      (body', tbody', texpr') <- checkMatch p body texpr
      pure ([(p, body')], tbody', texpr')
    checkMatches ((p, body) : ps) texpr =  do
      (body', tbody, texpr') <- checkMatch p body texpr
      (ps', tbody', texpr'') <- checkMatches ps texpr'
      body'' <- update tbody body' tbody'
      pure ((p, body'') :ps', tbody, texpr'')

    checkMatch p body texpr = do
      (newEnv, texpr') <- checkPattern p texpr env
      (body', tbody) <- typeCheck body newEnv
      pure (body', tbody, texpr')

    -- Check Pattern checks a single pattern given the type "provided" to it
    checkPattern :: TPattern -> EnvVal -> CheckEnv -> TI (CheckEnv, EnvVal)
    checkPattern TWildCardPat texpr env = pure (env, texpr)
    checkPattern (TBindPat s) texpr env = pure (Env.insert s texpr env, texpr)
    checkPattern (TVarPat id1 idx subPatterns ty) texpr env =
      -- ty = the "net" type of the variant
      -- TODO: what if the type of texpr needs to be inferred??
      case texpr of 
        -- TODO: check binding against the 
        -- TODO: check for duplicate bindings...
        -- TODO: implicit dependent type...
        Infer n -> 
          throwError "not checking inferred arguments in match-statements..."
          -- expr' <- update texpr expr ty
          -- -- TODO: what if the pattern instantiates a type?!
          -- let ity = alts !! idx
          --     loopSub (ptn:ptns) (ti:tis) env = do
          --       env' <- checkPattern ptn (Var ti) env 
          --       loopSub ptns tis env'
          --     loopSub [] [] env = pure env
               
          -- loopSub subPatterns ity env
        t -> do
          mty <- envToModulus t env
          case mty of 
            (MNamed id name types alts) ->
              if id == id1 then
                -- instance type 
                let ity = (alts !! idx)
                    loopSub :: [TPattern] -> [ModulusType] -> CheckEnv -> TI CheckEnv
                    loopSub (ptn:ptns) (ti:tis) env = do
                      (env', envval) <- checkPattern ptn (Var ti) env 
                      loopSub ptns tis env'
                    loopSub [] [] env = pure env
                     
                in do
                  -- TODO: some kind of recursive unification??
                  env' <- loopSub subPatterns ity env
                  pure (env', Var mty)
              else
                throwError "types do not match: expression/pattern"
            _ -> throwError ("type " <> show mty <> " cannot be matched")
         





-- typeCheck t env = do
--   throwError ("typecheck not implemented for intermediate: " <> show t)















-- UTILITY FUNCTIONS
  
getT :: Int -> TI ModulusType
getT n = do
  (m, _) <- get
  case Map.lookup n m of 
    Just x -> pure x
    Nothing -> throwError ("couldn't find modulus type at idx: " <> show n)

newT :: TI EnvVal  
newT = do
  (m, c) <- get
  let m' = Map.insert c (MVar ("#" <> show c)) m
  put (m', c+1)
  pure (Infer c)

bind :: Int -> ModulusType -> TI ()
bind n t = modify (\(f, s) -> (Map.insert n t f, s))

-- Update 
-- Update combines a coercion and unification:
-- If one of the two types is a type being inferred, then we use unification.
-- Otherwise, we attempt to coerce the type 
update :: EnvVal -> TIntermediate -> EnvVal -> TI TIntermediate
update (Val _ t1) expr (Infer y) = do
  t2 <- getT y
  t <- unify t2 t1 
  bind y t
  pure expr
update (Var t1) expr (Infer y) = do
  t2 <- getT y
  t <- unify t2 t1 
  bind y t
  pure expr
update (Infer x) expr (Val _ t2) = do
  t1 <- getT x
  t <- unify t1 t2 
  bind x t
  pure expr
update (Infer x) expr (Var t2) = do
  t1 <- getT x
  t <- unify t1 t2 
  bind x t
  pure expr
update (Infer x) expr (Infer y) = do
  t1 <- getT x
  t2 <- getT y
  t <- unify t1 t2 
  bind x t
  bind y t
  pure expr

-- Neither of the types are 
update (Var t1)   e (Var t2)   = coerce t1 e t2
update (Var t1)   e (Val _ t2) = coerce t1 e t2
update (Val _ t1) e (Var t2)   = coerce t1 e t2
update (Val _ t1) e (Val _ t2) = coerce t1 e t2

-- Coerce
-- Coerce gives us an expression and its' type, along with a type we want to
-- coerce that expression to have. To do this, we may need to perform some kind
-- of type application! This is like unification from the Hindler-Milner system,
-- with the expression being required because 
coerce :: ModulusType -> TIntermediate -> ModulusType -> TI TIntermediate
coerce t1 expr t2 = do
  (expr', _) <- coerce' t1 expr t2 Set.empty Map.empty
  pure expr'

coerce' :: ModulusType -> TIntermediate -> ModulusType
           -> Set.Set String -> Map.Map String ModulusType
           -> TI (TIntermediate, Map.Map String ModulusType)
-- coerce': like coerce, but we keep track of which variables can be substituted
  -- The only "important" clauses are the implicit ones: here, we add a given
  -- variable to the refill 
coerce' _t1 expr _t2 free subs = case (_t1, _t2) of 
  -- TODO: not sure what to do here...
  (ImplMDep t1 _ t2, ImplMDep t1' _ t2') -> do
    checkEq t1 t1'
    checkEq t2 t2'
    pure (expr, Map.empty)

  -- 
  (ImplMDep t1 s t2, t) -> do
    (expr, subs) <- coerce' t2 expr t (Set.insert s free) subs
    case Map.lookup s subs of 
      Just t  -> pure (expr, Map.delete s subs)
      Nothing -> pure (expr, subs)

  (t1, t2) -> do
    subs' <- subcoerce t1 t2 free subs
    pure (expr, subs')

  where 
    -- TODO: occurs-checks??
    -- subcoerce only finds the correct implicit substitution: it does not add
    -- new type-variables!
    subcoerce :: ModulusType -> ModulusType -> Set.Set String -> Map.Map String ModulusType
              -> TI (Map.Map String ModulusType)
    subcoerce (MVar v) t free subs =
      case Map.lookup v subs of
        Just t' -> do
          checkEq t t'
          pure subs
        Nothing -> if Set.member v free then
            pure (Map.insert v t subs)
          else if typeEq (MVar v) t then
              pure subs
            else
              throwError ("variable not free: " <> v)


    subcoerce (MArr t11 t12) (MArr t21 t22) free subs = do
      subs1 <- subcoerce t11 t12 free subs
      subs2 <- subcoerce t11 t12 free subs
      compose subs1 subs2

    subcoerce (MPrim p1) (MPrim p2) free subs =
      if p1 == p2 then
        pure subs
      else
        throwError ("cannot coerce non-equal primitive types "
                    <> show p1 <> " and " <> show p2)

    subcoerce (TypeN n1) (TypeN n2) free subs =
      if n1 == n2 then pure subs else throwError "cannot coerce unequal typeN's"

    subcoerce (MNamed id1 nme1 mtype1 alts1) (MNamed id2 nme2 mtype2 alts2) free subs = 
      if id1 == id2 then do
        subs_lst <- mapM (\(t1, t2) -> subcoerce t1 t2 free subs) (zip mtype1 mtype2)
        let foldrM f v [] = pure v
            foldrM f v (x:xs) = (f v x) >>= (\res -> foldrM f res xs)
        foldrM compose Map.empty subs_lst
      else 
        throwError ("cannot coerce non-equal variant types")
    subcoerce t1 t2 _ _ = throwError ("cannot coerce: " <> show t1 <> " " <> show t2)

    -- compose substitutions: if they conflict then throw an error
    compose :: Map.Map String ModulusType -> Map.Map String ModulusType
            -> TI (Map.Map String ModulusType)
    compose m1 m2 = do
      -- test if there is overlap!
      if Map.foldrWithKey (\k t b -> case Map.lookup k m2 of
                           Just t' -> not (typeEq t t') || b
                           Nothing -> b) False m1 then 
        throwError "overlap in variable substitution"
      else pure (Map.union m1 m2)
       



-- consideration: we cannot randomly coerce, e.g. a → a and b → b!! This is
-- because a and be may be bound elsewhere! We can unify ∀a.a→a and ∀b.b→b,
-- however! TODO: make unification compatible with this

-- Unification
-- Unification is very similar different to unification in the HM system, but
-- with some minor differences.
-- Normally, unification will try and find substitutions for type variables,
-- e.g. b → a and (c → int) would unify to give (c → int), as we can substitute
-- b for c and a for int on the LHS to get the RHS. Here, we can only make
-- substitutions (on the LHS) if 
-- TODO: add the set/checker!
unify :: ModulusType -> ModulusType -> TI ModulusType
unify _t1 _t2 = case (_t1, _t2) of
  (MArr t1 t2, MArr m1 m2) -> do
    t1' <- unify t1 m1 
    t2' <- unify t2 m2 
    pure (MArr t1' t2')
  (MVar v, MVar v') -> pure (MVar v')
  (MVar v,  t) ->
    if occursCheck v t then
      throwError "failed occurs check"
    else pure t 
  (t, MVar v) ->
    if occursCheck v t then
      throwError "failed occurs check"
    else pure t 
  (MPrim p, MPrim p') ->
    if p == p' then pure (MPrim p) else err
  (TypeN n1, TypeN n2) -> if n1 == n2 then pure (TypeN n1) else err

  (Signature m1, Signature m2) -> do 
    let m2' = Map.toList m2
    rList <- mapM (\(s, t) ->
                     case Map.lookup s m2 of
                       Just t' -> do
                         u <- unify t t' 
                         pure (s, u)
                       Nothing -> err) m2'
    pure (Signature (Map.fromList rList))
      
  (MDot t s, MDot t' s') ->
    if s == s' then
      throwError ("cannot unify unequal type-accesses: " <> s <> " and " <> s')
    else do
      u <- unify t t' 
      pure (MDot u s)

  -- TODO: potential infinite loop!
  (MDot t s, t2) ->
    case t of 
      Signature m -> case Map.lookup s m of 
        Just t -> unify t t2 
        Nothing -> throwError "couldn't find field in sig!"
      _ -> throwError "got field of non-sig type!"

  (t1, MDot t s) -> 
    case t of 
      Signature m -> case Map.lookup s m of 
        Just t -> unify t1 t 
        Nothing -> throwError "couldn't find field in sig!"
      _ -> throwError "got field of non-sig type!"

  (_, _) -> err
  where err  = throwError ("couldn't unify!" <> show _t1 <> " with " <> show _t2)





envToModulus :: EnvVal -> CheckEnv -> TI ModulusType  
envToModulus (Var m) env = pure m
envToModulus (Val _ m) env = pure m
envToModulus (Infer i) env = getT i

  
subtype :: ModulusType -> ModulusType -> Bool
subtype _t1 _t2 = case (_t1, _t2) of
  -- TODO: handle renaming...
  (TypeN n, TypeN n') -> n == n'
  (MVar s, MVar s') -> s == s'
  (MPrim t1, MPrim t2) -> t1 == t2
  (MArr t1 t2, MArr t1' t2') -> subtype t1 t1' && subtype t2 t2'
  (Signature m1, Signature m2) ->
    Map.foldrWithKey (\k t b -> case Map.lookup k m2 of
                         Just t' -> subtype t t' && b
                         Nothing -> False) True m1
  (_, _) -> False
    

checkEq :: ModulusType -> ModulusType -> TI ()  
checkEq t1 t2 =
  if typeEq t1 t2 then
    pure ()
  else
    throwError ("types not equal: " <> show t1 <> " and " <> show t2)
      



  


  

deduceType :: String -> ModulusType -> [ModulusType] -> Maybe ModulusType
deduceType s m [] = Nothing
deduceType nme fnc (t : ts) = 
  case fnc of 
    (MArr t1 t2) ->
      let c1 = unifiesTo nme t1 t
          c2 = deduceType nme t2 ts
      in case (c1, c2) of
        (Just l, Just r) -> do
          if typeEq l r then Just l else Nothing 
        (Just l, Nothing) -> Just l
        (Nothing, Just r) -> Just r
        (Nothing, Nothing) -> Nothing
    _ -> Nothing 

  where 
    unifiesTo :: String -> ModulusType -> ModulusType -> Maybe ModulusType
    unifiesTo s (MVar s') t
      | s == s' = Just t
      | otherwise = Nothing
    unifiesTo s (MArr l r) (MArr l' r') = 
      case (unifiesTo s l l', unifiesTo s r r') of 
        (Just l, Just r) -> if typeEq l r then Just l else Nothing 
        (Just l, Nothing) -> Just l
        (Nothing, Just r) -> Just r
        (Nothing, Nothing) -> Nothing
    unifiesTo _ _ _ = Nothing

-- The deduce module function takes
-- + A signature and it's name
-- + a type in which the name is bound 
-- + a set of constraints (i.e. applications) 
-- + an environment 
-- It will then try and find a *unique* module in the environment which matches the
-- constraints. 
-- For example,
-- + The signature is Ord and it is bound to string O, where the signature Ord
--   requires has field t with type type.
-- + The function type is (x : O.t) → (y : O.t) → bool
-- + The constraints are [int, int]
-- Then, the function will try and find a module matching the Ord signature, but
-- with t = int! If there are either none, or more than one, then an error will
-- be thrown.
deduceModule :: SigMap -> String -> ModulusType -> [ModulusType] -> CheckEnv
             -> TI TIntermediate
deduceModule sig nme fnc constraints env = 
  case fnc of 
    (MArr t1 t2) -> do
      mdleSpec <- specialiseSig sig nme fnc constraints 
      searchFor sig mdleSpec env
    _ -> throwError "module deduction failed as cannot deal with non MArr type!" 
  where
    -- specialiseSig will, for a given module with type sig, which is bound to
    -- name nme within a (function) type, and the modulus-types which the functions'
    -- arguments are instantiated with, return a constraint on any module bound
    -- to nme, in the form of a map of which values have to be mapped to which
    -- variables.
    -- This module-constraint can then be used to find a matching module in the
    -- environment

    -- TODO: specialise this to more than single-field access!
    specialiseSig :: SigMap -> String -> ModulusType -> [ModulusType] -> TI SigMap
    -- TODO implementation for not just MArr!
    specialiseSig sig nme (MArr (MDot (MVar s) var) ret) (t:ts) = do
      let mp = if nme == s then Map.singleton var t else Map.empty
      tl <- specialiseSig sig nme ret ts
      -- TODO: check for overlap, e.g. (t = int and t = bool) => error
      pure (Map.union mp tl)
    specialiseSig sig nme ty (t:ts) = specialiseSig sig nme ty ts
    specialiseSig _ _ _ [] = pure Map.empty
    
    searchFor :: SigMap -> SigMap -> CheckEnv -> TI TIntermediate
    searchFor sig constraints env = do 
      (inferMap, _) <- get
      -- TODO: unions hide shadowed values: is this desirable??
      let (envMap, tMap) = Env.toMap env
          envMap' = Map.map toMls envMap 
          tMap' = Map.map typeEnv tMap 
          finMap = Map.union envMap' tMap'

          -- TODO: this is to compensate for bad type inference...
          toMls (Val v t) = let (Right t') = runExcept (typeExpr v) in Left (v, t')
          toMls (Var t) = Right t
          toMls (Infer n) = let (Just v) = Map.lookup n inferMap in Right v

          typeEnv v = let (Right t) = runExcept (typeExpr v) in Left (v, t)

          -- Check if the module 
          -- 1. Matches the signature sig
          -- 2. Matches the constraints imposed by the arguments
          matchModule (Left (v, t1)) = 
            -- TODO: part 1 (above)
            if not (hasType v (Signature sig)) then
              False
            else
              case v of 
                (Module m) -> 
                  Map.foldrWithKey (\k t b -> case Map.lookup k m of
                                       Just maybet' -> case maybet' of
                                         Type t' -> typeEq t t' && b
                                         _ -> False
                                       Nothing -> False) True constraints
                _ -> False
          matchModule (Right t1) = False

      case Map.toList (Map.filter (matchModule) finMap) of 
        [(_, Left (v, t))] -> pure (TValue v)
        [(s, _)] -> pure (TSymbol s)
        [] -> throwError ("failed to find unique module with signature: " <> show (Signature sig)
                         <> " and constraints: " <> show constraints)
                         -- <> "given the map:  "
                         -- <> (Map.foldrWithKey (\k v s ->
                         --     k <> ": " <> show v <> "\n" <> s) --  "" finMap))
        l -> throwError ("too many candidates for  unique module with signature: "
                         <> show (Signature sig) <> " and constraints: " <> show constraints <> "\n"
                         <> "got: " <> show l)


-- depType: given a value
-- + if it is a type return that type
-- + if it is a module, return the (dependent) type of that module
-- Intended to be used so arguments to 'dependent' functions can be converted
-- into types, and then substituted in to make sure it all works!
depType :: TIntermediate -> TI (ModulusType)
depType (TValue (Type t)) = pure t
depType (TValue (Module m)) = do 
  lst <- mapM (\(s, v) -> do
                   t' <- depType (TValue v)
                   pure (Just (s, t'))
                   `catchError` (\_ -> pure Nothing)) (Map.toList m)
  --lst :: [(Maybe (String, ModulusType))]
  let lst' = foldr (\v tl -> case v of
                       Just x -> x : tl
                       Nothing -> tl) [] lst
  pure (Signature (Map.fromList lst'))

depType v = throwError ("cannot get as dep-type: " <> show v)



