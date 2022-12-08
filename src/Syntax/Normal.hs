{-# LANGUAGE TemplateHaskell, TypeSynonymInstances, FlexibleInstances#-}
{-# LANGUAGE FlexibleContexts, RankNTypes, GADTs #-}

module Syntax.Normal (Pattern(..),
                      CoPattern(..),
                      Modifier(..),
                      Normal(..),
                      Neutral(..),
                      ProgState(..),
                      ArgType(..),
                      IEThread(..),
                      AST(..),
                      PrimVal(..),
                      PrimType(..),
                      CollVal(..),
                      CollTy(..),
                      InbuiltCtor(..),
                      Special(..),
                      Thunk(..),
                      uid_counter,
                      var_counter,
                      thunk_map,
                      dropMod,
                      peelMod,
                      addMod,
                      toEmpty) where

import Data.Text (Text, pack, unpack)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import qualified Data.Set as Set
import qualified Data.Map as Map

import Foreign.Ptr (FunPtr, Ptr)
import Foreign.C.Types (CDouble, CInt)  
import Foreign.C.String (CString)  
  
import Control.Lens hiding (Context, Refl)
import Control.Monad.State (MonadState, StateT) 
import Control.Monad.Except (MonadError, ExceptT) 
import Control.Monad.Reader (MonadReader,ReaderT)

import Bindings.Libtdl
import Syntax.Expression



data Pattern m
  = WildCard
  | VarBind String (Normal m)
  | MatchInduct Int Int [Pattern m]
  | MatchModule [(String, Pattern m)]
  | InbuiltMatch (Normal m -> (Normal m -> Pattern m -> m (Maybe [(String, (Normal m, Normal m))]))
                           -> m (Maybe [(String, (Normal m, Normal m))]))


data CoPattern m
  = CoWildCard
  | CoVarBind String (Normal m)
  | CoMatchInduct String Int Int [CoPattern m]
  | CoMatchModule [(String, CoPattern m)]
  -- | InbuiltMatch (Normal -> (Normal -> Pattern -> EvalM (Maybe [(String, Normal)]))
  --                        -> EvalM (Maybe [(String, Normal)]))


instance Show (Pattern m) where  
  show WildCard = "_"
  show (VarBind sym _) = sym
  show (MatchInduct _ _ _) = "inductive match"
  show (InbuiltMatch _) = "inbuilt match"


instance Show (CoPattern m) where  
  show CoWildCard = "_"
  show (CoVarBind sym _) = sym
  show (CoMatchInduct _ _ _ _) = "coinductive match"


newtype Thunk = Thunk { tid :: Int }
  deriving (Show, Eq, Ord)


data Special
  -- Definition Forms 
  = Def | Induct | Coinduct | Open | LetOpen | ClassInstance
  -- Control Flow 
  | If | MkMatch | MkCoMatch
  -- Value Constructors
  | Let | Lambda |  MkHandler | MkStructure 
  -- Type Constructors
  | MkSig | MkProd  
  -- Syntax-Manipulation
  | MkQuote | Do  | Access | Mac |  Annotate
  -- Foreign function stuf 
  | ForeignAdapter
  deriving (Eq, Show)


data PrimVal
  = Unit
  | Bool Bool
  | Int Integer
  | Nat Integer
  | Float Float
  | Char Char
  | String Text

  -- TODO: plugin system!!
  | CInt CInt
  | CDouble CDouble
  | CString CString
  deriving Eq


-- IndPat :: allows defining a constructor match pair
--           used for defining values (list List) that we
--           want access to from haskell
data InbuiltCtor m
  --       name    pattern-match
  = IndPat String
           ([Pattern m] -> Normal m
                        -> (Normal m -> Pattern m
                        -> m (Maybe [(String, (Normal m, Normal m))]))
                        -> m (Maybe [(String, (Normal m, Normal m))]))
           -- strip, ctor & type
           Int (Normal m) (Normal m)


data CollTy m
  = MaybeTy (Normal m)
  | ListTy (Normal m)
  | ArrayTy (Normal m)
  | IOMonadTy (Normal m)
  -- TODO: plugin
  | CPtrTy (Normal m)


data CollVal m
  = MaybeVal (Maybe (Normal m)) (Normal m)
  | ListVal [Normal m] (Normal m)
  | ArrayVal (Vector (Normal m)) (Normal m)
  | IOAction (IEThread m) (Normal m)
  -- TOOD: plugin
  | CPtr (Ptr ())


data IEThread m
  = IOThread (IO (IEThread m))
  | MThread (m (IEThread m))
  | Pure (m (Normal m))
  | Bind (m (IEThread m)) (m (Normal m))
  | Seq (m (IEThread m)) (m (IEThread m))


data Modifier m = Implicit | MInstance (Normal m) | Private 
  deriving (Show, Eq)


-- m is the type of monad inside the object

data ArgType = Visible | Hidden | Instance
  deriving (Show, Eq, Ord)

data Normal m
  -- Neutral term
  = Neu (Neutral m) (Normal m)
  -- Basic & Inbuilt Values and Types
  | PrimVal PrimVal 
  | PrimType PrimType
  | CollVal (CollVal m)
  | CollTy (CollTy m)
  | PropEq (Normal m) (Normal m)
  | Refl (Normal m)
  | InbuiltCtor (InbuiltCtor m)

  -- Universes
  | NormUniv Int 

  -- Dependent Products & Functions
  | NormProd String ArgType (Normal m) (Normal m)
  | NormArr (Normal m) (Normal m)
  | NormAbs String (Normal m) (Normal m)

  | Builtin (Normal m -> m (Normal m)) (Normal m)
  -- TOOD: BuiltinLzy should take a thunk! (?)
  | BuiltinLzy (m (Normal m) -> m (Normal m)) (Normal m)
  
  -- Structures & Signatures
  | NormSct [(String, (Normal m, [Modifier m]))] (Normal m)
  | NormSig [(String, Normal m)]

  -- Inductive and Coinductive Types and Values
  --   NormIVal : name, tyid, valid, strip, vals, type
  --   NormCoVal: tyid, a record of functions
  --                (name, id, vars, func-body)
  --   NormCoDtor : name, tyid, strip, type
  | NormIType String Int [Normal m]
  | NormIVal String Int Int Int [Normal m] (Normal m)
  | NormCoType String Int [Normal m]
  | NormCoVal [(CoPattern m, m (Normal m))] (Normal m)
  | NormCoDtor String Int Int Int Int [Normal m] (Normal m)

  -- Multi-Stage Programming
  | BuiltinMac ([AST m] -> m (AST m))
  | Special Special
  | Keyword String
  | Symbol String 
  | AST (AST m)

  -- Foreign values
  | NormCModule CModule      -- a foreign library
  | NormCValue CValue (Normal m) -- a foreign value + its' type


data Neutral m
  = NeuVar String (Normal m)
  -- an inbuilt function waiting on a netural term
  | NeuApp (Neutral m) (Normal m)
  | NeuDot (Neutral m) String
  | NeuIf (Neutral m) (Normal m) (Normal m) (Normal m)
  | NeuMatch (Neutral m) [(Pattern m, Normal m)] (Normal m)
  | NeuCoMatch (Neutral m) [(CoPattern m, Normal m)]
  | NeuBuiltinApp (Normal m -> m (Normal m)) (Neutral m) (Normal m)


data AST m
  = Atom (Normal m)
  | Cons [AST m]


data PrimType
  = BoolT | SpecialT | CharT | IntT | NatT | FloatT | UnitT | StringT | AbsurdT
  -- TODO: refactor ctypes via a plugin system!
  | CModuleT | CIntT | CDoubleT | CStringT
  | MacroT
  deriving (Eq, Ord)
  

data ProgState m = ProgState
  { _uid_counter   :: Int
  , _var_counter   :: Int
  , _thunk_counter :: Int
  , _thunk_map :: Map.Map Thunk (Either (m (Normal m, Normal m)) (Normal m, Normal m))
  }



instance Show (Normal m) where
  show (Neu neu _)      = show neu
  show (PrimVal prim)   = show prim
  show (PrimType prim)  = show prim
  show (CollTy ty)      = show ty
  show (CollVal val)    = show val
  show (Refl ty)        = "refl " <> show ty
  show (PropEq v1 v2)   = (show v1) <> "≡" <> (show v2)
  show (InbuiltCtor pat) = show pat
  show (NormUniv n) = if n == 0 then "𝒰" else "𝒰" <> show n
  show (NormProd var argType a b) =
    let (l, r) = case argType of 
          Visible -> ("(", ")")
          Hidden -> ("{", "}")
          Instance -> ("⦃", "⦄")
    in
      l <> var <> ":" <> show a <> r <> " → " <> show b
  show (NormArr l r) =
    let l' = if fncLike l then "(" <> show l <> ")" else show l
        in l' <> " → " <> show r
  show (NormAbs var body ty) = "(λ [" <> var <> "] " <> show body <> ")"
  show (Builtin _ ty) = "(fnc : " <> show ty <> ")"
  show (BuiltinLzy _ ty) = "(lfnc : " <> show ty <> ")"
  show (NormSct fields ty) =
    if isTuple fields then
      showAsTuple fields
    else
      "(structue" <> (foldr
                      (\(f, (val, _)) str -> str <> (" (def " <> f <> " " <> show val <> ")"))
                      "" (reverse fields)) <> ")"
    where 
      isTuple fields = foldr (\(n, (_, _)) b -> (n == "_1" || n == "_2") && b) True fields && not (null fields)
      showAsTuple fields = 
        case ((getField "_1" . dropMod) fields, (getField "_2" . dropMod) fields) of 
          (Just v1, Just v2) -> "(" <> show v1 <> ", " <> show v2 <> ")"
  show (NormSig fields) =
    if isTuple fields then
      showAsTuple fields
    else
      "(signature" <> (foldr
                       (\(f, val) str -> str <> (" (" <> f <> " : " <> show val <> ")"))
                       "" (reverse fields)) <> ")"
    where 
      isTuple fields = foldr (\(n, _) b -> (n == "_1" || n == "_2") && b) True fields && not (null fields)
      showAsTuple fields = 
        case (getField "_1" fields, getField "_2" fields) of 
          (Just v1, Just v2) -> "(" <> show v1 <> " * " <> show v2 <> ")"

  
  show (NormIType name _ params) =
    name <> (foldr (\p s -> " " <> show p <> s) "" params)
  show (NormIVal name _ _ _ params ty) = 
    name <> (foldr (\p s -> " " <> show p <> s) "" (reverse params))

  show (NormCoType name _ params) =
    name <> (foldr (\p s -> " " <> show p <> s) "" params)
  show (NormCoDtor name _ _ len _ args ty) = 
    name <> " : " <> show ty <> " len: " <> show len <> " args: " <> show args
  show (NormCoVal _ ty) =
    "(covalue : " <> show ty <> ")"
  show (BuiltinMac _) = show "<inbuilt-macro>"
  show (Special sp) = show sp
  show (Keyword word) = "⁖" <> word
  show (Symbol sym) = "<" <> sym <> ">"
  show (AST ast) = "AST" <> show ast
  show (NormCModule _) = "<c-module>"
  show (NormCValue _ ty) = "<cvalue: " <> show ty <> ">"


instance Show (Neutral m) where
  show (NeuVar var _) = var
  show (NeuApp neu (Neu (NeuApp n1 n2) ty)) =
    show neu <> " (" <> show (Neu (NeuApp n1 n2) ty) <> ")"
  show (NeuApp neu norm) = show neu <> " " <> show norm
  show (NeuDot neu field) = show neu <> "." <> field 
  show (NeuMatch neu pats _) = "(match " <> show neu
    <> foldr (\(p, e) s -> s <> "\n" <> show p <> " → " <> show e) "" (reverse pats)
    <> ")"
  show (NeuCoMatch neu pats) = "(comatch " <> show neu
    <> foldr (\(p, e) s -> s <> "\n" <> show p <> " → " <> show e) "" (reverse pats)
    <> ")"
  show (NeuIf cond e1 e2 _) = "(if " <> show e1 <> " " <> show e2 <> ")"

  show (NeuBuiltinApp fn neu ty)  = "((<builtin> " <> show neu <> ") : " <>  show ty <> ")"


  
instance Show PrimType where 
  show BoolT   = "Bool"
  show SpecialT = "Special"
  show IntT    = "ℤ"
  show NatT    = "ℕ"
  show UnitT   = "Unit"
  show FloatT  = "Float"
  show CharT   = "Char"
  show StringT = "String"
  show AbsurdT = "Absurd"

  show MacroT  = "Macro"
  show CIntT   = "CInt"
  show CDoubleT  = "CDouble"
  show CStringT  = "CString"
  show CModuleT  = "CModule"


instance Show PrimVal where   
  show e = case e of  
    Unit -> "()"
    Int x -> show x
    Float f -> show f
    Bool x -> if x then "true" else "false"
    Char c -> show c
    String str -> show str
    CString str -> show str
    CDouble d -> show d

  
instance Show (CollVal m) where   
  show e = case e of  
    -- TODO: pretty-printing for lists & arrays
    MaybeVal (Just l) _ -> "some " <> show l
    MaybeVal Nothing _ -> "none"
    ListVal l _ -> show l
    ArrayVal v _ -> case length v of
      n | n == 0 -> "⦗⦘"
        | n == 1 -> "⦗" <> show (v Vector.! 0) <> "⦘"
        | otherwise -> Vector.foldl (\str v -> str <> " " <> show v)
                             ("⦗" <> show (Vector.head v))
                             (Vector.tail v)
                       <> "⦘"
    IOAction _ ty -> "<_ : IO " <> show ty <> ">" 
    CPtr _ -> "<cptr>" 

instance Show (CollTy m) where   
  show e = case e of  
    MaybeTy ty -> "Maybe " <> show ty
    ListTy ty -> "List " <> show ty
    ArrayTy n1 -> "Array " <> show n1
    IOMonadTy ty -> "IO " <> show ty
    CPtrTy ty -> "CPtr " <> show ty

instance Show (InbuiltCtor m) where
  show (IndPat sym _ _ _ ty) = show sym <> " " <> show ty

instance Show (AST m) where
  show e = "AST: " <> show_ast e
    where
      show_ast (Cons [x]) = "(" <> show_ast x <>  ")"
      show_ast (Cons (x:xs)) = "(" <> show_ast x <> foldr (\s1 s2 -> " " <> show_ast s1 <> s2) ")" xs   
      show_ast (Atom x) = show x 
  

dropMod :: [(a, (b, c))] -> [(a, b)]
dropMod ((x, (y, _)) : xs) = (x, y) : dropMod xs
dropMod [] = []

peelMod :: [(a, (b, c))] -> ([(a, b)], [c])
peelMod lst = peelMod' lst ([], [])
  where
    peelMod' ((x, (y, z)) : xs) (al, ar) = ((x, y) : al, z : ar)
    peelMod' [] accum = accum
  
addMod :: [(a, b)] -> [c] -> [(a, (b, c))]
addMod a b = zipWith (\(x, y) z -> (x, (y, z))) a b

toEmpty :: [(a, b)] -> [(a, (b, [c]))]
toEmpty = map (\(x, y) -> (x, (y, [])))

getField f ((f', n):xs) = if f == f' then Just n else getField f xs
getField f [] = Nothing

fncLike :: (Normal m) -> Bool
fncLike (NormArr _ _)        = True
fncLike (NormProd _ _ _ _)     = True
fncLike _ = False



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


instance Eq (Neutral m) where
  a == b = neu_equiv a b (Set.empty, 0) (Map.empty, Map.empty)
  
  
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

instance Expression (Normal m) where 
  free (Builtin _ _) = Set.empty
  free (PrimType  _) = Set.empty
  free (NormUniv  _) = Set.empty
  free (PrimVal   _) = Set.empty
  free (CollTy ty) = case ty of 
    ListTy a -> free a
    ArrayTy a -> free a
    IOMonadTy a -> free a
    CPtrTy a -> free a
  free (CollVal val) = case val of 
    ListVal lst ty -> foldr (Set.union . free) (free ty) lst
    IOAction _ ty -> free ty

  free (Neu neutral ty) = Set.union (free neutral) (free ty)
  free (NormProd var _ a b) =
    Set.union (free a) (Set.delete var (free b))
  free (NormArr a b) =
    Set.union (free a) (free b)
  free (NormIVal _ _ _ _ norms ty) = foldr (Set.union . free) Set.empty norms
  free (NormIType _ _ norms) = foldr (Set.union . free) Set.empty norms
  free (NormSig fields) = foldl (\set (field, val) ->
                                   Set.delete field (Set.union (free val) set)) Set.empty fields

  rename s1 s2 norm = case norm of
    (Neu neutral ty) -> Neu (rename s1 s2 neutral) (rename s1 s2 ty)
    (Builtin fn ty) -> Builtin fn (rename s1 s2 ty)
    (PrimType  t)   -> PrimType t
    (NormUniv  u)   -> NormUniv u
    (PrimVal   v)   -> PrimVal v
    (CollTy ty) -> CollTy $ case ty of 
      ListTy a -> ListTy $ rename s1 s2 a
      ArrayTy a -> ArrayTy (rename s1 s2 a)
      IOMonadTy a -> IOMonadTy $ rename s1 s2 a
    (CollVal val) -> CollVal $ case val of 
      ListVal lst ty -> ListVal (map (rename s1 s2) lst) (rename s1 s2 ty) 
      IOAction action ty -> IOAction action (rename s1 s2 ty)

    (NormProd var aty a b) ->
      if var == s1 then
        NormProd var aty (rename s1 s2 a) b
      else 
        NormProd var aty (rename s1 s2 a) (rename s1 s2 b)
    (NormArr a b) -> NormArr (rename s1 s2 a) (rename s1 s2 b)
    -- (NormIVal _ _ _ _ norms ty) = foldr (Set.union . rename) Set.empty norms
    -- (NormIType _ _ norms) = foldr (Set.union . rename) Set.empty norms
    (NormSig fields) ->
      NormSig (renameFields fields)
      where renameFields [] = []
            renameFields ((field, val):fields) = 
              if field == s1 then
                (field, val):fields
              else 
                (field, rename s1 s2 val):renameFields fields


instance Expression (Neutral m) where
  free (NeuVar var ty) = Set.insert var (free ty)
  free (NeuApp l r) = (free l) <> (free r)
  free (NeuDot sig field) = (free sig)
  free (NeuIf cond e1 e2 ty) = free cond <> free e1 <> free e2 <> free ty
  free (NeuMatch term alts ty) =
      free term <> (foldr (Set.union . altfree) Set.empty alts) <> free ty
    where
      altfree (p, e) = foldr (Set.delete) (patVars p) (free e)
  free (NeuBuiltinApp _ _ _) = Set.empty

  rename s1 s2 neu = case neu of  
    (NeuVar var ty) ->
      if var == s1 then
        NeuVar s2 (rename s1 s2 ty)
      else
        NeuVar var (rename s1 s2 ty)
    (NeuApp l r) -> NeuApp (rename s1 s2 l) (rename s1 s2 r)

patVars :: Pattern m -> Set.Set String
patVars WildCard = Set.empty
patVars (VarBind sym _) = Set.singleton sym
patVars (MatchInduct id1 id2 subpats) = foldr Set.union Set.empty (map patVars subpats)

$(makeLenses ''ProgState)
