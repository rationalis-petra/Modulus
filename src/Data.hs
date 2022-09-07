{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Data where

import Data.Text (Text, pack, unpack)
import Data.Vector (Vector)
import Control.Lens hiding (Context)
import Control.Monad.State (State) 
import Control.Monad.Except (ExceptT) 
import Control.Monad.Reader (ReaderT) 
  
import qualified Data.Map as Map
import qualified Data.Set as Set

-- type Context = Map.Map String Expr
-- type TypeContext' = TypeContext ProgMonad

data Environment = Environment {
  localCtx      :: Map.Map String (Normal' EvalM),
  currentModule :: Normal,
  globalModule  :: Normal
}

data Definition
  = SingleDef String Core Normal
  | InductDef String Int [(String, Normal)] Normal [(String, Int, Normal)] 
  | EffectDef String [String] [(String, [Core])]
  | OpenDef Core [(String, Normal)]
  deriving Show

data Pattern
  = WildCard
  | VarBind String 
  | MatchInduct Int Int [Pattern]
  | MatchModule [(String, Pattern)]
  deriving Show

data Core
  = CNorm Normal                     -- Normalised value
  | CVar String                      -- Variable
  | CDot Core String                 -- Access a field from a struct/signature
  | CArr Core Core                   -- Arrow Type (degenerate product)
  | CProd String Core Core           -- Dependent Product 
  | CImplProd String Core Core       -- Dependent Product 
  | CAbs String Core Normal          -- Function abstraction
  | CApp Core Core                   -- Function application 
  | CMAbs String Normal Core         -- Macro abstraction
  | CSeq [Core]                      -- Sequence Effects
  | CLet [(String, Core)] Core       -- Local binding
  | CLetOpen [(Core, [(String, Core)])] Core  -- Local opens
  | CMatch Core [(Pattern, Core)]    -- Pattern-Match
  -- TODO: remove this via lazy functions!
  | CIf Core Core Core
  -- | Hndl Core Core                       -- Handle with a handler
  -- | MkHndler [(String, [String], Core)]  -- Create a new handler
  | CSct [Definition]                -- Structure Definition
  | CSig [Definition]                -- Signature Definition (dependent sum)
  deriving Show


data TopCore = TopDef Definition | TopExpr Core


-- Contexts:   
-- globCtx: global context -- used to store modules etc.
-- evalCtx: context used for evaluation -- this context can also capture values,
--          e.f. from let-bindings
-- typeCtx: context used for the coalescence/type-checking phase


data Special
  -- Definition Forms 
  = Def | Induct | Coinduct | Open | LetOpen
  -- Control Flow 
  | If | MkMatch
  -- Effects
  | HandleAsync | Handle | HandleWith | MkEffect | Seq
  -- Value Constructors
  | Let | Lambda |  MkHandler | MkStructure 
  -- Type Constructors
  | MkSig | MkProd  
  -- Syntax-Manipulation
  | MkQuote | Do  | Access | Mac |  Annotate
  deriving Show


data PrimVal
  = Unit
  | Bool Bool
  | Int Integer
  | Float Float
  | Char Char
  | String Text
  deriving Eq


data CollE m
  = List [(Normal' m)]
  | Vector (Vector (Normal' m))



-- m is the type of monad inside the object
type Normal = Normal' EvalM
type Neutral = Neutral' EvalM
  
data Normal' m  
  -- Basic Values and Types
  = Neu (Neutral' m)
  | PrimVal PrimVal 
  | PrimType PrimType
  | NormArrTy (Normal' m)
  | NormUniv Int 

  -- Dependent Products & Functions
  | NormProd String (Normal' m) (Normal' m)
  | NormImplProd String (Normal' m) (Normal' m)
  | NormArr (Normal' m) (Normal' m)
  | NormAbs String (Normal' m) (Normal' m)

  | Builtin (Normal' m -> m (Normal' m)) (Normal' m)
  
  -- Structures & Signatures
  | NormSct [(String, Normal' m)]
  | NormSig [(String, Normal' m)]

  -- Inductive (later. Coinductive) datatypes
  | NormIType String Int [Normal]
  | NormIVal String Int Int [Normal] Normal

  -- Effects
  | IOAction Int Int ([Normal' m] -> IO (m (Normal' m))) [Normal' m]

  -- Multi-Stage Programming
  | BuiltinMac ([AST] -> m AST)
  | Special Special
  | Keyword String
  | Symbol String 
  | AST AST
  -- stuff related to macros etc.
  | Undef

data Neutral' m
  = NeuVar String 
  -- an inbuilt function waiting on a netural term
  | NeuApp (Neutral' m) (Normal' m)
  | NeuDot (Neutral' m) String
  | NeuIf (Neutral' m) (Normal' m) (Normal' m)
  | NeuMatch (Neutral' m) [(Pattern, Normal)]

  | NeuBuiltinApp (Normal' m -> m (Normal' m)) (Neutral' m) (Normal' m)
  | NeuBuiltinApp2 (Normal' m -> Normal' m -> m (Normal' m)) (Neutral' m) (Normal' m)
  | NeuBuiltinApp3 (Normal' m -> Normal' m -> Normal' m -> m (Normal' m)) (Neutral' m) (Normal' m)
  | NeuBuiltinApp4 (Normal' m -> Normal' m -> Normal' m -> Normal' m -> m (Normal' m)) (Neutral' m) (Normal' m)
  

  
--   -- ALGEBRAIC EFFECTS
--   | IOEffect
--   | IOAction Int Int ([Value m] -> IO (m (Value m))) [Value m]
--   | Effect Int Int
--   | Action Int Int Int [Value m]
--   | CHandler [(Int, Int, [String], Core)]


-- data AST = Atom Expr | Cons AST 
data AST
  = Atom Normal
  | Cons [AST]


data MaybeEffect m a 
  = RaiseAction (Normal' (ActionMonadT m) -> ActionMonadT m a)
                Int
                Int
                [Normal' (ActionMonadT m)]
                (Maybe ([Normal' (ActionMonadT m)]
                        -> IO ((ActionMonadT m) (Normal' (ActionMonadT m)))))
  | Value a




instance Show (Normal' m) where
  show (Neu neu) = show neu
  show (PrimVal prim) = show prim
  show (PrimType prim) = show prim
  show (NormArrTy tn) = "Vector" <> show tn
  show (NormUniv n) = if n == 0 then "𝒰" else "𝒰" <> show n

  show (NormProd var a b) = "(" <> var <> ":" <> show a <> ")" <> " → " <> show b
  show (NormImplProd var a b) = "{" <> var <> ":" <> show a <> "}" <> " → " <> show b
  show (NormArr l r) = show l <> " → " <> show r
  show (NormAbs var body ty) = "(λ " <> var <> " . " <> show body <> ")"
  show (Builtin _ ty) = show "(fnc : " <> show ty <> ")"

  
  show (NormSct fields) =
    "(structue" <> (foldr
                (\(f, val) str -> str <> (" (def " <> f <> " " <> show val <> ")"))
                "" (reverse fields)) <> ")"
  show (NormSig fields) =
    "(signature" <> (foldr
                (\(f, val) str -> str <> (" (" <> f <> " : " <> show val <> ")"))
                "" (reverse fields)) <> ")"

  
  show (NormIType name id params) =
    name <> (foldr (\p s -> " " <> show p <> s) "" params)
  show (NormIVal name tid id params ty) = 
    name <> (foldr (\p s -> " " <> show p <> s) "" (reverse params))

  show (IOAction _ _ _ _) = "IO-Action"

  show (BuiltinMac _) = show "<inbuilt-macro>"
  show (Special sp) = show sp
  show (Keyword word) = "&" <> word
  show (Symbol sym) = "<" <> sym <> ">"
  show (AST ast) = "AST" <> show ast

  show Undef = "$Undef"

instance Show (Neutral' m) where
  show (NeuVar var) = var
  show (NeuApp neu (Neu (NeuApp n1 n2))) = show neu <> " (" <> show (Neu (NeuApp n1 n2)) <> ")"
  show (NeuApp neu norm) = show neu <> " " <> show norm
  show (NeuDot neu field) = show neu <> "." <> field 
  show (NeuMatch neu pats) = "(match " <> show neu 
                             <> foldr (\(p, e) s -> s <> "\n" <> show p <> " → " <> show e) "" (reverse pats)
                             <> ")"
  show (NeuIf cond e1 e2) = "(if " <> show e1 <> " " <> show e2 <> ")"

  show (NeuBuiltinApp fn neu ty)  = "(fnc :" <> show ty  <> ") " <> show neu
  show (NeuBuiltinApp2 fn neu ty) = "(fnc :" <> show ty  <> ") "  <> show neu
  show (NeuBuiltinApp3 fn neu ty) = "(fnc :" <> show ty  <> ") "  <> show neu
  show (NeuBuiltinApp4 fn neu ty) = "(fnc :" <> show ty  <> ") "  <> show neu
-- TODO: effect type



  
data PrimType = BoolT | CharT | IntT | FloatT | UnitT | StringT | AbsurdT
  deriving (Eq, Ord)
  

type EvalEnvM env = ActionMonadT (ReaderT env (ExceptT String (State ProgState)))
type EvalM = EvalEnvM Environment
  

newtype ActionMonadT m a = ActionMonadT (m (MaybeEffect m a))

data ProgState = ProgState { _uid_counter :: Int, _var_counter :: Int }  


  
instance Show PrimType where 
  show BoolT   = "Bool"
  show IntT    = "Int"
  show UnitT   = "Unit"
  show FloatT  = "Float"
  show CharT   = "Char"
  show StringT = "String"
  show AbsurdT = "Absurd"


instance Show PrimVal where   
  show e = case e of  
    Unit -> "()"
    Int x -> show x
    Float f -> show f
    Bool x -> if x then "true" else "false"
    Char c -> show c
    String str -> show str

  
instance Show (CollE m) where   
  show e = case e of  
    Data.List l -> show l
    Data.Vector v -> show v

instance Show AST where
  show e = "AST: " <> show_ast e
    where
      show_ast (Cons lst) = "(" <> foldr (\s1 s2 -> show_ast s1 <> " " <> s2) ")" lst   
      show_ast (Atom x) = show x 
  

$(makeLenses ''ProgState)
