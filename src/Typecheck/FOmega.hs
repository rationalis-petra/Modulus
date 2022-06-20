module Typecheck.FOmega where

import qualified Data.Map as Map
import Data(PrimType(..), PrimE(..))
import Control.Monad.Except (Except, throwError, catchError)
import Control.Monad.State (State, StateT, lift, get, modify)

import Data.String  

type Row a = [(Lab, a)]

-- instance Show a => Show (Row a) where  
--   show (Row r) = show r
type InferMonad = StateT (Map.Map String Int) (Except String)

type Var = String
type Lab = String

data Env = Env {typ :: (Map.Map Var Kind), val :: (Map.Map Var Type)}
emptyEnv = Env Map.empty Map.empty
initialState = Map.empty

lookupType :: Var -> Env -> InferMonad Kind
lookupType v (Env {typ=typ}) = case Map.lookup v typ of
  Just x -> pure x
  Nothing -> throwError ("cannot find type : " <> v)
insertType :: Var -> Kind -> Env -> Env
insertType v k env =
  env { typ = Map.insert v k (typ env) }

lookupVal :: Var -> Env -> InferMonad Type
lookupVal v (Env {val=val}) = case Map.lookup v val of 
  Just x -> pure x
  Nothing -> throwError ("cannot find val : " <> v)
insertVal :: Var -> Type -> Env -> Env
insertVal v t env =
  env { val = Map.insert v t (val env) }

listAssoc :: Lab -> Row a -> Maybe a
listAssoc l ((l', v) : xs) = 
  if l == l' then Just v else listAssoc l xs
listAssoc l [] = Nothing


data Kind
  = BaseK 
  | ArrK Kind Kind
  | RcdK (Row Kind) 
  deriving Eq

data Type
  = VarT Var
  | PrimT PrimType 
  | LamT Var Kind Type 
  | RecT (Row Type)        -- signature (module type)
  | ArrT Type Type         -- Function type
  | AppT Type Type         -- type constructor invocation 
  | AllT Var Kind Type     -- the forall type
  | ExistsT Var Kind Type  -- the there exists type
  | AccessT Type Lab       -- accessing a type field 
  | TInfer Int
    

data Expr
  = VarE Var
  | PrimE PrimE
  | IfE Expr Expr Expr  
  | RecE (Row Expr)      -- structures/modules
  | AccessE Expr Lab       -- field access
  | LetE Var Expr Expr     -- let, should be obvious...
  | LamE Var Type Expr     -- λ abstraction
  | GenE Var Kind Expr     -- Λ abstraction
  | AppE Expr Expr          -- value application
  | Inst Expr Type         -- type application
  | PackE Type Expr Type   -- pack & unpack, for existentials
  | Unpack Expr Var Var Expr
  deriving Show

-- Infer/Check the type of an expression
-- DONE
inferExpr :: Expr -> Env -> InferMonad Type
inferExpr e env = case e of 
  VarE v -> lookupVal v env
  PrimE p -> pure $ PrimT (typePrim p)
  IfE cnd e1 e2 -> do
    checkExp e1 (PrimT BoolT) env
    t <- inferExpr e1 env
    checkExp e2 t env
    pure t
    `catchError`
    (\e -> throwError ("err in IfE: " <> e))
  RecE rows -> do
    -- TODO: mutual type-inference via laziness
    let (lbls, exprs) = unzip rows
    types <- mapM (swap inferExpr env) exprs 
    pure $ RecT $ zip lbls types

  AccessE rcd lbl -> do
    t <- inferExpr rcd env
    case t of 
      RecT rows -> case listAssoc lbl rows of 
        Just v -> pure v
        Nothing -> throwError ("couldn't find label " <> lbl)
      x -> throwError ("expecting signature, got" <> show x)

  LetE v e1 e2 -> do
    t <- inferExpr e1 env
    inferExpr e2 (insertVal v t env) 

  GenE v k e -> do    -- Λ abstraction
    t <- inferExpr e (insertType v k env)
    pure $ AllT v k t 

  LamE x t e -> do
    t' <- inferExpr e (insertVal x t env)
    pure (ArrT t t')

  AppE e1 e2 -> do     -- value application
    t <- inferExpr e1 env
    case t of 
      ArrT t1 t2 -> do
        checkExp e2 t1 env
        pure t2
        `catchError` (\e -> throwError ("tr AppE: " <> e))
      x -> throwError ("expecting → type, got " <> show x)

  Inst e t -> do         -- type application
    _t <- inferExpr e env
    case _t of 
      AllT v k t' -> do
        checkType t k env
        substType t' [(v, t)]
        `catchError` (\e -> throwError("tr Inst: " <> e))

  PackE t1 e t2 -> do   -- pack & unpack, for existentials
    checkType t2 BaseK env 
    case t2 of  
      ExistsT a k t3 -> do
        checkType t1 k env
        nt <- (substType t3 [(a, t1)])
        checkType nt k env
        pure t2
      x -> throwError ("expecting E, got " <> show x)
    `catchError` (\e -> throwError ("tr PackE: " <> e))
  Unpack e1 a1 x e2 -> do
    t1 <- inferExpr e1 env 
    case t1 of 
      ExistsT a2 k t2 -> do
        t' <- substType t2 [(a2, VarT a1)]
        let update = (insertVal x t') . (insertType a1 k)
        t <- inferExpr e2 (update env) 
        checkType t BaseK env
        pure t
      x -> throwError ("expecting E, got " <> show x)
    `catchError` (\e -> throwError ("tr UnpackE: " <> e))

typePrim :: PrimE -> PrimType 
typePrim e = case e of 
  Unit -> UnitT
  Bool _ -> BoolT
  Int _ -> IntT
  Float _ -> FloatT
  Char _ -> CharT
  String _ -> StringT

  
  -- TODO
inferType :: Type -> Env -> InferMonad Kind
inferType t env = case t of
  VarT v -> lookupType v env
  PrimT _ -> pure BaseK
  ArrT t1 t2 -> do
    checkType t1 BaseK env
    checkType t2 BaseK env 
    pure BaseK
  RecT tr -> do
    let (lbls, exprs) = unzip tr
    kinds <- mapM (swap inferType env) exprs 
    pure $ RcdK $ zip lbls kinds
  AllT a k t -> do
    checkType t BaseK (insertType a k env)
    pure BaseK
  ExistsT a k t -> do
    checkType t BaseK (insertType a k env)
    pure BaseK
  LamT a k t -> do 
    k' <- inferType t (insertType a k env)
    pure (ArrK k k')
  AppT t1 t2 -> do
    k <- inferType t1 env 
    case k of 
      ArrK k1 k2 -> do
        checkType t2 k1 env
        pure k2
      _ -> throwError "error in AppT: kind of t1 not ArrK"
  AccessT t l -> do
    k <- inferType t env
    case k of 
      RcdK kr -> case listAssoc l kr of 
        Just k -> pure k
        Nothing -> throwError ("couldn't find label " <> l <> " in AccessT")
      k -> throwError ("expecting Record kind, got " <> show k)
  


checkExp :: Expr -> Type -> Env -> InferMonad ()
checkExp expr ty env = do
  ty' <- inferExpr expr env  
  eq <- typeEq ty ty'
  if eq then
    pure ()
  else
    throwError ("err: types not equal" <> show ty <> ", " <> show ty')

checkType :: Type -> Kind -> Env -> InferMonad ()
checkType ty k env = do
  k' <- inferType ty env  
  if k == k' then pure ()
  else throwError ("err: kinds not equal" <> show k <> ", " <> show k')
    
-- Substitutions 
substType :: Type -> [(Var, Type)] -> InferMonad Type
substType t s = case t of 
  PrimT t -> pure (PrimT t)
  VarT a  -> case listAssoc a s of 
    Just x -> pure x
    Nothing -> pure (VarT a)
  RecT lst -> do
    lst' <- mapM (\(l, t) -> (substType t s >>= (\t' -> pure (l, t')))) lst
    pure (RecT lst')
  AccessT t lbl -> do
    t' <- substType t s
    pure (AccessT t' lbl)
  ArrT t1 t2 -> do
    t1' <- (substType t1 s)
    t2' <- (substType t2 s)
    pure (ArrT t1' t2')
  AppT t1 t2-> do
    t1' <- (substType t1 s)
    t2' <- (substType t2 s)
    pure (AppT t1' t2')
  LamT a k t -> do
    a' <- rename a
    t' <- (substType t ((a, VarT a') : s))
    pure (LamT a' k t')
  AllT a k t -> do
    a' <- rename a
    t' <- (substType t ((a, VarT a') : s))
    pure (AllT a' k t')
  ExistsT a k t -> do
    a' <- rename a
    t' <- (substType t ((a, VarT a') : s))
    pure (ExistsT a' k t')


-- Renaming  
    
typeEq :: Type -> Type -> InferMonad Bool  
typeEq t1 t2 = do
  t1' <- (normType t1)
  t2' <- (normType t2)
  eq t1' t2'
  where
    eq (VarT a1) (VarT a2) = pure (a1 == a2)
    eq (PrimT t1) (PrimT t2) = pure (t1 == t2)
    eq (ArrT t11 t12) (ArrT t21 t22) = (&&) <$> eq t11 t21 <*> eq t12 t22
    eq (RecT tr1) (RecT tr2) =
      forallM (\((l1, t1), (l2, t2)) -> (&&) <$> pure (l1 == l2) <*> (eq t1 t2)) (zip tr1 tr2)
      where
        forallM f (x : xs) = f x >>= (\b -> if b then forallM f xs else pure False)
        forallM f [] = pure True
    eq (AllT a1 k1 t1) (AllT a2 k2 t2) =
      (&&) <$> pure (k1 == k2) <*> (substType t2 [(a2, VarT a1)] >>= typeEq t1 )
    eq (ExistsT a1 k1 t1) (ExistsT a2 k2 t2) =
      (&&) <$> pure (k1 == k2) <*> (substType t2 [(a2, VarT a1)] >>= typeEq t1)
    eq (LamT a1 k1 t1) (LamT a2 k2 t2) =
      (&&) <$> pure (k1 == k2) <*> (substType t2 [(a2, VarT a1)] >>= typeEq t1)
    eq (AppT t11 t12) (AppT t21 t22) =
      (&&) <$> eq t11 t21 <*> eq t12 t22
    eq (AccessT t1 l1) (AccessT t2 l2) =
      (&&) <$> eq t1 t2 <*> pure (l1 == l2)
    eq _ _ = pure False



-- Normalisation: "fold away" redundant types. For example, the type
-- (∀ α. α → α) int         becomes   int → int, and
-- {x : int, y : bool}.int  beomes    int
normType :: Type -> InferMonad Type
normType t = case t of 
  ArrT t1 t2 -> do
    t1' <- (normType t1)
    t2' <- (normType t2)
    pure $ ArrT t1' t2'  
  RecT row -> (mapM (\(l, t) -> normType t >>= pure . ((,) l)) row) >>= (pure . RecT)
  AllT a k t -> (AllT a k) <$> (normType t) 
  ExistsT a k t -> (ExistsT a k) <$> (normType t) 
  LamT a k t -> pure $ LamT a k t -- NOTE: lambda is not normalized/research lam vs All
  AppT t1 t2 -> do
    t1' <- normType t1
    case t1' of 
      LamT a k t -> (substType t [(a, t2)]) >>= normType
      t1' -> (AppT t1') <$> normType t2
  AccessT t l -> do
    t' <- normType t
    case t' of
      RecT tr -> case listAssoc l tr of 
        Just x -> normType x
        Nothing -> throwError ("cannot find label " <> l <> " in type "
                                      <> show t' <> "when normalising")
      t' -> pure (AccessT t' l)
  t -> pure t



-- Renaming  
-- renaming is needed as follows: 
-- suppose we have a type signature ∃ f. ∀ a. a → f a 
-- but we want to rename f -> a 
-- then, we get ∀ a. a → a a!! 
-- this is bad :( -> we need to rename a so that things are kept nice :)
basename :: Var -> Var
basename x = strTil '#' x
  where strTil c (s : ss)
          | s == c = []
          | otherwise = s : (strTil c ss)
        strTil c [] = []

  
-- renameFor vars x = 
--   let x' = basename x
--       iter i = 
   
rename :: Var -> InferMonad Var
rename x = do
  vm <- get
  let x' = basename x
  let n = (case Map.lookup x' vm of
             Just n -> (n + 1)
             Nothing -> 0)
  modify (Map.insert x' n)
  pure $ x' <> "#" <> show n
      

swap f x y = f y x  




-- Show instances

instance Show Kind where
  show BaseK = "w"
  show (ArrK (ArrK k1' k1'') k2) = "(" <> show (ArrK k1' k1'') <> ") -> " <> show k2
  show (ArrK k1 k2) = show k1 <> " -> " <> show k2
  show (RcdK row) = show row


instance Show Type where  
  show (VarT v) = v
  show (PrimT pt) = show pt 
  show (LamT v k t) = "fn " <> v <> ":" <> show k <> " -> " <> show t
  show (RecT row) = show row
  show (ArrT (ArrT t1' t1'') t2) = "(" <> show (ArrT t1' t1'') <> ") -> " <> show t2
  show (ArrT (AllT v k t) t2) = "(" <> show (AllT v k t) <> ") -> " <> show t2
  show (ArrT (ExistsT v k t) t2) = "(" <> show (ExistsT v k t) <> ") -> " <> show t2
  show (ArrT t1 t2) = show t1 <> " -> " <> show t2

  
  show (AppT (AppT t1' t1'') t2) = "(" <> show (AppT t1' t1'') <> ") " <> show t2
  show (AppT (ArrT t1' t1'') t2) = "(" <> show (ArrT t1' t1'') <> ") " <> show t2
  show (AppT (AllT v k t) t2) = "(" <> show (AllT v k t) <> ") " <> show t2
  show (AppT (ExistsT v k t) t2) = "(" <> show (ExistsT v k t) <> ") " <> show t2
  show (AppT t1 t2) = show t1 <> " " <> show t2

  show (AllT v k t) = "A " <> v <> ":" <> show k <> " . " <> show t
  show (ExistsT v k t) = "E " <> v <> ":" <> show k <> " . " <> show t
  show (AccessT t1 l) = show t1 <> "." <> show l
