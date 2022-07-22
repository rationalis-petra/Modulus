{-# LANGUAGE TemplateHaskell #-}
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

data ValContext = ValContext {
  localCtx      :: Map.Map String Expr,
  currentModule :: Expr,
  globalModule  :: Expr
}
type Context = ValContext

type SigDefn = Map.Map String ModulusType
data Definition
  = SingleDef String Core ModulusType
  | VariantDef String [String] Int [(String, Int, [ModulusType])] ModulusType
  | EffectDef  String [String] [(String, [Core])]
  | OpenDef Core SigDefn
  deriving (Show)

data Pattern
  = WildCard
  | VarBind String 
  --             id  n   sub-patterns
  | MatchVariant Int Int [Pattern]
  | MatchModule [(String, Pattern)]
  deriving Show

data Core
  = CVal Expr                            -- A value
  | CSym String                          -- Symbols
  | CDot Core String                     -- Access a field from a struct/signature
  | CAbs String Core ModulusType         -- Function abstraction
  | CApp Core Core                       -- Function application 
  | CMAbs String ModulusType Core        -- Macro abstraction
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
  | Handle | HandleAsync | HandleWith | MkModule
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
  = List [(Object m)]
  | Vector (Vector (Object m))

-- m is the type of monad inside the object
-- c is the type of the interpreted "code"
data Object m
  -- Inbuilt Datatypes 
  = PrimE PrimE
  | Coll (CollE m) 
  | Keyword String
  | Type ModulusType
  | Variant String Int Int [Object m]
  | Constructor String Int Int Int [Object m]
  | CConstructor String Int Int Int [String] [Object m] ModulusType
  | Module (Map.Map String (Object m))

  -- Pattern matching on inbuilt data-types nargs currying
  | CustomCtor Int [(Object m)]
    -- constructor
    ([Object m] -> m (Object m))
    -- matcher
    (Object m -> m (Maybe [(Object m)]))
    -- type
    ModulusType
  -- TODO: pattern-matching on structures.

  -- Syntax and macros
  | AST AST
  | Symbol String
  | Special Special
  | Macro [String] Intermediate ValContext
  | InbuiltMac ([AST] -> m AST)


  -- EVALUATION & FUNCTIONS
  | Function [String] Intermediate ValContext
  | CFunction String Core ValContext ModulusType 
  | InbuiltFun (Object m -> m (Object m)) ModulusType

  -- ALGEBRAIC EFFECTS
  | IOEffect
  | IOAction Int Int ([Object m] -> IO (m (Object m))) [Object m]
  | Effect Int Int
  | Action Int Int Int [Object m]
  | Handler [(Int, Int, [String], Intermediate)]


-- arguments to functions may have optional type annotations
data Arg = Sym String | Annotation String Intermediate
  deriving Show


data IDefinition
  = ISingleDef String Intermediate
  | IVariantDef String [String] [(String, [Intermediate])] 
  | IEffectDef  String [String] [(String, [Intermediate])]
  | IOpenDef Intermediate
  deriving (Show)

-- Untyped (typed) intermediate
data Intermediate
  = IValue Expr
  | IDefinition IDefinition
  | IApply Intermediate Intermediate
  | IImplApply Intermediate Intermediate
  | IQuote AST
  | IAccess Intermediate String
  | IDo [Intermediate]
  | IProgn [Intermediate]
  | IIF Intermediate Intermediate Intermediate
  | ISymbol String
  | ILet [(String, Intermediate)] Intermediate
  | ILetOpen [Intermediate] Intermediate
  | ILambda [(Arg, Bool)] Intermediate
  | IMacro [Arg] Intermediate
  | IModule [IDefinition] 
  | ISignature [IDefinition] 
  | IHandle Intermediate [(String, [String], Intermediate)]
  | IMkHandler [(String, [String], Intermediate)]
  | IHandleWith Intermediate Intermediate
  | IMatch Intermediate [(IPattern, Intermediate)]
  deriving Show

data IPattern
  = ISingPattern String
  | IWildCard
  | ICheckPattern Intermediate [IPattern]
  deriving Show

-- data AST = Atom Expr | Cons AST 
data AST
  = Atom Expr
  | Cons [AST]

data MaybeEffect m a 
  = RaiseAction (Object (ActionMonadT m) -> ActionMonadT m a)
                Int
                Int
                [Object (ActionMonadT m)]
                (Maybe ([Object (ActionMonadT m)]
                        -> IO ((ActionMonadT m) (Object (ActionMonadT m)))))
  | Value a


  
  
data PrimType = BoolT | CharT | IntT | FloatT | UnitT | StringT 
  deriving (Eq, Ord)

data Kind = K | To Kind Kind

data ModulusType
  = TypeN Int
  | MVar String
  | Signature (Map.Map String ModulusType)
  | MArr ModulusType ModulusType
  | MDep ModulusType String ModulusType
  | ImplMDep ModulusType String ModulusType
  | MDot ModulusType String
  | MEffect (Set.Set EffectType) ModulusType
  --        id  name   params        instance-types           
  |  MNamed Int String [ModulusType] [[ModulusType]]

  -- "Primitive" / native types
  | MPrim PrimType
  | MVector ModulusType

  -- BAD -> we want him gone!
  | Undef
  | Large
  deriving (Eq, Ord)

data EffectType
  = IOEff
  | CustomEff Int [ModulusType]  
  deriving (Show, Eq, Ord)

type Expr = Object EvalM

type EvalM = ActionMonadT (ReaderT Context (ExceptT String (State ProgState)))

newtype ActionMonadT m a = ActionMonadT (m (MaybeEffect m a))

data ProgState = ProgState { _uid_counter :: Int, _var_counter :: Int }  


instance Show PrimType where 
  show BoolT   = "bool"
  show IntT    = "int"
  show UnitT   = "unit"
  show FloatT  = "float"
  show CharT   = "char"
  show StringT = "string"

instance Show ModulusType where
  show (MPrim p) = show p
  show (Undef) = "undefined"
  show (Large) = "large"
  show (MVar s) = s

  show (MArr (MArr t1 t2) t3) =
    "(" <>  show (MArr t1 t2) <> ") → " <> show t3
  -- show (MArr (MDep t1 s t2) t3) =
  --   show (MDep t1 s t2) <> " → " <> show t3
  show (MArr t1 t2) = show t1 <> " → " <> show t2  

  -- show (MDep (MDep t1 s t2) s2 t3) =
  --   "(" <>  s <> ":" <> show (MDep t1 s t2) <> ") → " <> show t3
  show (MDep t1 s t2) = "(" <> s <> ":" <> show t1 <> ") → " <> show t2 
  show (ImplMDep (TypeN 1) s t2) = "{" <> s <> "} → " <> show t2
  show (ImplMDep t1 s t2) = "{" <> s <> ":" <> show t1 <> "} → " <> show t2
  show (MDot t s) = show t <> "." <> s 

  show (TypeN n) = case n of 
    0 -> "type"
    1 -> "type₁"
    2 -> "type₂"
    n -> "type" ++ show n
  -- TODO branch on isLarge!
  show (Signature map) =
    "(sig " <> drop 2 (Map.foldrWithKey show_sig "" map) <> ")"
    where show_sig key t str = 
            str <> ", " <> key <> " : " <> show t
  show (MNamed id name types _) = 
    name <> foldr (\t str -> " " <> show t <> str) "" types

  show (MVector t) = "Vector " ++ show t

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

instance Show (Object a) where  
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

    Function args bdy _ -> "<λ " <> show args ++ " -> " ++ show bdy ++ ">"
    CFunction _ _ _ t -> "<fnc> :: " <> show t
    InbuiltFun _ t -> "<fnc> :: " <> show t

    InbuiltMac _ -> "<mac> :: "
    Macro args bdy _ -> "<mac " <> show  args <> " -> " <> show bdy <> ">"
  
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

  
