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
  localCtx      :: Map.Map String (Value EvalM),
  currentModule :: Expr,
  globalModule  :: Expr
}

type SigDefn = Map.Map String TypeExpr
data Definition
  = SingleDef String Core TypeExpr
  | VariantDef String [String] Int [(String, Int, [TypeNormal])] TypeNormal
  | EffectDef  String [String] [(String, [Core])]
  | OpenDef Core SigDefn
  deriving Show

data Pattern
  = WildCard
  | VarBind String 
  | MatchVariant Int Int [Pattern]
  | MatchModule [(String, Pattern)]
  deriving Show

data Core
  = CVal Expr                            -- A value
  | CSym String                          -- Symbols
  | CDot Core String                     -- Access a field from a struct/signature
  | CAbs String Core TypeNormal          -- Function abstraction
  | CApp Core Core                       -- Function application 
  | CMAbs String TypeNormal Core         -- Macro abstraction
  | CSeq [Core]                          -- Sequence Effects
  | CLet [(String, Core)] Core           -- Local binding
  | CLetOpen [(Core, SigDefn)] Core      -- Local opens
  | CMatch Core [(Pattern, Core)]        -- Pattern-Match
  -- TODO: remove this via lazy functions!
  | CIF Core Core Core
  -- | Hndl Core Core                       -- Handle with a handler
  -- | MkHndler [(String, [String], Core)]  -- Create a new handler
  | CMod [Definition]                -- Module Definition
  | CSig [Definition]                -- Signature Definition
  deriving Show


data TopCore = TopDef Definition | TopExpr Core


-- Contexts:   
-- globCtx: global context -- used to store modules etc.
-- evalCtx: context used for evaluation -- this context can also capture values,
--          e.f. from let-bindings
-- typeCtx: context used for the coalescence/type-checking phase


data Special
  -- Forms which define new values 
  = Def | DefVariant | If | Let | Lambda | Mac | MkHandler
  | Handle | HandleAsync | HandleWith | MkStructure
  | MkQuote | MkMatch | MkEffect | Open | LetOpen
  | Do | Seq | Access | MkSig | Annotate
  deriving Show


data PrimE
  = Unit
  | Bool Bool
  | Int Integer
  | Float Float
  | Char Char
  | String Text


data CollE m
  = List [(Value m)]
  | Vector (Vector (Value m))


-- m is the type of monad inside the object
-- c is the type of the interpreted "code"
data Value m
  -- Inbuilt Datatypes 
  = PrimE PrimE
  | Coll (CollE m) 
  | Keyword String
  | Type TypeNormal
  | Variant String Int Int [Value m]
  | Constructor String Int Int Int [Value m]
  | CConstructor String Int Int Int [String] [Value m] TypeNormal
  | Module (Map.Map String (Value m))

  -- Pattern matching on inbuilt data-types nargs currying
  | CustomCtor Int [(Value m)]
    -- constructor
    ([Value m] -> m (Value m))
    -- matcher
    (Value m -> m (Maybe [(Value m)]))
    -- type
    TypeNormal
  -- TODO: pattern-matching on structures.

  -- Syntax and macros
  | AST AST
  | Symbol String
  | Special Special
  -- TODO: change to [String], figure out resultant errors in macroEval  
  | CMacro String Core Environment TypeNormal
  | InbuiltMac ([AST] -> m AST)

  -- EVALUATION & FUNCTIONS
  | CFunction String Core Environment TypeNormal 
  | InbuiltFun (Value m -> m (Value m)) TypeNormal

  -- ALGEBRAIC EFFECTS
  | IOEffect
  | IOAction Int Int ([Value m] -> IO (m (Value m))) [Value m]
  | Effect Int Int
  | Action Int Int Int [Value m]
  | CHandler [(Int, Int, [String], Core)]


-- data AST = Atom Expr | Cons AST 
data AST
  = Atom Expr
  | Cons [AST]


data MaybeEffect m a 
  = RaiseAction (Value (ActionMonadT m) -> ActionMonadT m a)
                Int
                Int
                [Value (ActionMonadT m)]
                (Maybe ([Value (ActionMonadT m)]
                        -> IO ((ActionMonadT m) (Value (ActionMonadT m)))))
  | Value a



data TypeExpr
  = TyNorm TypeNormal
  | TyVar String
  | TyArr TypeExpr TypeExpr
  | TyDep String TypeExpr TypeExpr
  | TyImplDep String TypeExpr TypeExpr
  | TyApp TypeExpr TypeExpr
  | TySig [(String, TypeExpr)]
  | TyDot TypeExpr String

-- Normal: expressions
data TypeNormal
  = Neu TypeNeutral
  | NormPrim PrimType 
  | NormVector TypeNormal
  | NormUniv Int
  | NormDep String TypeNormal TypeNormal
  | NormImplDep String TypeNormal TypeNormal
  | NormArr TypeNormal TypeNormal
  | NormSig [(String, TypeNormal)]

  | Undef
  deriving Show

-- Neutral: a subset of normal expressions, these expressions cannot be
-- evaluated further due to missing a variable application (i.e. normalisation
-- within the body of a function). They include no introduction forms, only
-- elimination forms.
data TypeNeutral  
  = NeuVar String
  | NeuApp TypeNeutral TypeNormal
  | NeuImplApp TypeNeutral TypeNormal
  | NeuDot TypeNeutral String
  deriving Show
  

-- TODO: effect type

class Variable a where   
  fromString :: String -> a
  toString :: a -> String

instance Variable String where
  fromString = id
  toString = id
  
data PrimType = BoolT | CharT | IntT | FloatT | UnitT | StringT | AbsurdT
  deriving (Eq, Ord)
  

type Expr = Value EvalM

type EvalEnvM env = ActionMonadT (ReaderT env (ExceptT String (State ProgState)))
type EvalM = EvalEnvM Environment
  

newtype ActionMonadT m a = ActionMonadT (m (MaybeEffect m a))

data ProgState = ProgState { _uid_counter :: Int, _var_counter :: Int }  


  
instance Show PrimType where 
  show BoolT   = "bool"
  show IntT    = "int"
  show UnitT   = "unit"
  show FloatT  = "float"
  show CharT   = "char"
  show StringT = "string"
  show AbsurdT = "absurd"


instance Show TypeExpr where
  show (TyNorm n) = "Normal: " <> show n
  show (TyVar var) = var

  show (TyArr (TyArr t1 t2) t3) =
    "(" <>  show (TyArr t1 t2) <> ") → " <> show t3
  show (TyArr t1 t2) = show t1 <> " → " <> show t2  

  -- show (MDep (MDep t1 s t2) s2 t3) =
  --   "(" <>  s <> ":" <> show (MDep t1 s t2) <> ") → " <> show t3
  show (TyDep var t1 t2) = "(" <> var <> ":" <> show t1 <> ") → " <> show t2 
  show (TyImplDep var t1 t2) = "{" <> var <> ":" <> show t1 <> "} → " <> show t2
  show (TyDot t s) = show t <> "." <> s 

  -- TODO branch on isLarge!
  show (TySig map) =
    "(sig " <> drop 2 (foldr show_sig "" map) <> ")"
    where show_sig (key, t) str = 
            str <> ", " <> show key <> " : " <> show t



instance Show PrimE where   
  show e = case e of  
    Unit -> "()"
    Int x -> show x
    Float f -> show f
    Bool x -> show x
    Char c -> show c
    String str -> show str

  
instance Show (CollE m) where   
  show e = case e of  
    Data.List l -> show l
    Data.Vector v -> show v

instance Show (Value a) where  
  show e = case e of
    PrimE x -> show x
    Keyword str -> "&" <> str
    AST ast -> show ast
    Coll c -> show c

    Special s -> "<special:" <> show s <> ">"
    Module map -> "(struct " <> drop 2 (Map.foldrWithKey show_entry "" map) <> ")"
      where show_entry key v str =
              (str <> ", " <> key <> " = " <> show v)
    Symbol str -> "<sym "  ++ str ++ ">"

    Variant s _ _ l -> s <> (foldl (\x y -> x <> " " <> y) "" (map show l))
    Constructor s _ _ 0 _ -> s
    Constructor s _ _ nargs l -> s <> " : " <> show nargs

    CConstructor s _ _ 0 _ [] _ -> s
    CConstructor s _ _ n _ nargs _ -> s <> foldr (\v s -> " " <> show v <> s) "" nargs

    CustomCtor _ _ _ _ _ -> "Custom Ctor"

    CFunction _ _ _ t -> "<fnc> :: " <> show t
    InbuiltFun _ t -> "<fnc> :: " <> show t

    InbuiltMac _ -> "<mac> :: "
  
    Type t -> show t

    IOAction id1 id2 _ _ -> "<ioction " ++ show id1 ++ show id2 ++ ">"
    Action id1 id2 size _ ->
      foldl (<>) "<act " [show id1, ",", show id2, ": ", show size,  ">"]

instance Show AST where
  show e = "AST: " <> show_ast e
    where
      show_ast (Cons lst) = "(" <> foldr (\s1 s2 -> show_ast s1 <> " " <> s2) ")" lst   
      show_ast (Atom x) = show x 
  

$(makeLenses ''ProgState)
