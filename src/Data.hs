{-# LANGUAGE TemplateHaskell, TypeSynonymInstances, FlexibleInstances#-}
{-# LANGUAGE FlexibleContexts, RankNTypes, GADTs #-}

module Data (Pattern(..),
             CoPattern(..),
             Modifier(..),
             Normal(..),
             Neutral(..),
             EvalT(..),
             Eval,
             Environment(..),
             ProgState(..),
             uid_counter,
             var_counter,
             thunk_map,
             dropMod,
             peelMod,
             addMod,
             toEmpty,
             IEThread(..),
             AST(..),
             PrimVal(..),
             PrimType(..),
             CollVal(..),
             CollTy(..),
             InbuiltCtor(..),
             Special(..),
             Thunk(..)) where

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

data Environment m = Environment {
  localCtx      :: Map.Map String (Either (Normal m, Normal m) Thunk),
  currentModule :: Normal m,
  globalModule  :: Normal m
}


data Special
  -- Definition Forms 
  = Def | Induct | Coinduct | Open | LetOpen
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


data Modifier = Implicit
  deriving (Show, Eq, Ord)


-- m is the type of monad inside the object

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
  | NormProd String (Normal m) (Normal m)
  | NormImplProd String (Normal m) (Normal m)
  | NormArr (Normal m) (Normal m)
  | NormAbs String (Normal m) (Normal m)

  | Builtin (Normal m -> m (Normal m)) (Normal m)
  -- TOOD: BuiltinLzy should take a thunk! (?)
  | BuiltinLzy (m (Normal m) -> m (Normal m)) (Normal m)
  
  -- Structures & Signatures
  | NormSct [(String, (Normal m, [Modifier]))] (Normal m)
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
  show (NormProd var a b) = "(" <> var <> ":" <> show a <> ")" <> " → " <> show b
  show (NormImplProd var a b) = "{" <> var <> ":" <> show a <> "}" <> " → " <> show b
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
  show (Keyword word) = "&" <> word
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

  show (NeuBuiltinApp fn neu ty)  = "((fn " <> show neu <> ") : " <>  show ty <> ")"

  
data PrimType
  = BoolT | SpecialT | CharT | IntT | NatT | FloatT | UnitT | StringT | AbsurdT
  -- TODO: refactor ctypes via a plugin system!
  | CModuleT | CIntT | CDoubleT | CStringT
  | MacroT
  deriving (Eq, Ord)
  

newtype EvalT m a = EvalT { unEvalT :: ReaderT (Environment (EvalT m)) (ExceptT String (StateT (ProgState (EvalT m)) m)) a }
type Eval = EvalT Identity


data ProgState m = ProgState
  { _uid_counter   :: Int
  , _var_counter   :: Int
  , _thunk_counter :: Int
  , _thunk_map :: Map.Map Thunk (Either (m (Normal m, Normal m)) (Normal m, Normal m))
  }


  
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
fncLike (NormImplProd _ _ _) = True
fncLike (NormProd _ _ _)     = True
fncLike _ = False

$(makeLenses ''ProgState)


