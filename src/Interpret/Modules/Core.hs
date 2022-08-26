module Interpret.Modules.Core (coreStructure) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map

import Data
import Interpret.Eval (liftFun2, liftFun4)
import Interpret.Transform
import qualified Interpret.Environment as Env

-- import Typecheck.Typecheck2 (subtype)


-- helper functions
get_symlist [] = Just []
get_symlist ((Symbol s) : args) =
  case get_symlist args of
    Just syms -> Just $ s : syms
    Nothing -> Nothing
get_symlist _ = Nothing

get_bindlist :: [Expr] -> Maybe ([String], [Expr])
get_bindlist [] = Just ([], [])
get_bindlist ((Symbol s) : val : bindings) =
  case get_bindlist bindings of
    Just (syms, vals) -> Just $ ((s : syms), (val : vals))
    Nothing -> Nothing
get_bindlist _ = Nothing

toDefs :: [AST] -> EvalM [AST]
toDefs (Cons [Atom (Symbol s), val] : tl) = do
  tl' <- toDefs tl
  pure (Cons [Atom (Special Def), Atom (Symbol s), val] : tl')
toDefs [] = pure []
toDefs _ = lift $ throwError "error: expected symbol value pair"

  
  -- MACROS
opDot :: [AST] -> EvalM AST
opDot [(Cons (op : xs)), rhs] = 
  pure $ (Cons [op, (Cons xs), rhs])
opDot args =  lift $ (throwError $ "bad args to macro: dot " ++ show args)
mlsDot = InbuiltMac opDot

defStructure :: [AST] -> EvalM AST
defStructure (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom (Special MkStructure) : bdy)])
defStructure _ = lift $ throwError "Bad Number of to macro: module" 
mlsDefStructure = InbuiltMac defStructure

defStruct :: [AST] -> EvalM AST
defStruct (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom mlsStruct : bdy)])
defStruct _ = lift $ throwError "Bad Number of to macro: module" 
mlsDefStruct = InbuiltMac defStruct

defSig :: [AST] -> EvalM AST
defSig (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom (Special MkSig) : bdy)])
defSig _ = lift $ throwError "Bad Number of to macro: module" 
mlsDefSig = InbuiltMac defSig

defFun :: [AST] -> EvalM AST
defFun (sym : fncdef) = 
  pure $ (Cons [Atom (Special Def), sym, Cons (Atom (Special Lambda) : fncdef)])
defFun args =  lift $ throwError $ "bad args to macro: defn" ++ show args
mlsDefun = InbuiltMac defFun

defMac :: [AST] -> EvalM AST
defMac [sym, symlist, bdy] = 
  pure $ Cons [Atom (Special Def), sym, Cons [Atom (Special Mac), symlist, bdy]]
defMac args =  lift $ throwError $ "bad args to macro: defsyntax" ++ show args
mlsDefmac = InbuiltMac defMac


--- Structures
with :: Expr -> Expr -> EvalM Expr 
with (Module m1) (Module m2) = 
  pure $ Module (Map.foldrWithKey Map.insert m1 m2)
with _ _ = lift $ throwError "bad args to with expected types"
mlsWith = liftFun2 with (NormArr Undef (NormArr Undef Undef))

upd :: [AST] -> EvalM AST
upd [mdle, Cons bindlist] = do
  mldebdy <- toDefs bindlist 
  pure $ Cons [(Atom mlsWith), mdle, Cons (Atom (Special MkStructure) : mldebdy)]
upd _ = lift $ throwError "bad args to macro: | "
mlsUpd = InbuiltMac upd

struct :: [AST] -> EvalM AST
struct bindlist = do
  mldebdy <- toDefs bindlist 
  pure $ Cons (Atom (Special MkStructure) : mldebdy)
mlsStruct = InbuiltMac struct

sig :: [AST] -> EvalM AST
sig bindlist = do
  mldebdy <- toDefs bindlist 
  pure $ Cons (Atom (Special MkSig) : mldebdy)
mlsSig = InbuiltMac struct

mlsNode = CustomCtor 1 [] nodeCtor nodeDtor Undef
  where
    nodeCtor :: [Expr] -> EvalM Expr
    nodeCtor [e] = 
      case e of
        Coll (List lst) -> to_ast lst >>= (pure . AST . Cons)
        (CustomCtor 0 [] c _ _) -> do
          out <- c [] -- (\x -> Just [x]) <$> (c [])
          case out of 
            Coll (List lst) -> to_ast lst >>= (pure . AST . Cons)
            _ -> lift $ throwError "cannot provide non-list to Node: "
        x -> lift $ throwError ("cannot provide non-list Node: " <> show x)
    nodeCtor _ = lift $ throwError "Node ctor requires exactly 1 args"

    to_ast :: [Expr] -> EvalM [AST]
    to_ast [] = pure []
    to_ast (AST x : xs) = do
      tl <- to_ast xs
      pure (x : tl)
    to_ast _ = lift $ throwError "must provide an AST list to Node"

    nodeDtor :: Expr -> EvalM (Maybe [Expr])
    nodeDtor val = 
      case val of
        AST (Cons lst) -> pure $ Just [(Coll $ List (map AST lst))]
        _ -> pure Nothing 

mlsAtom = CustomCtor 1 [] atomCtor atomDtor Undef
  where
    atomCtor :: [Expr] -> EvalM Expr
    atomCtor [x] = pure $ AST (Atom x)
    atomCtor _ = lift $ throwError "too many args to nil not have a ctor"

    atomDtor :: Expr -> EvalM (Maybe [Expr])
    atomDtor val = 
      case val of
        AST (Atom x) -> pure $ Just [x]
        _ -> pure Nothing 

-- mlsMacroExpand = liftFun macroExpand Undef Undef
--   where
--     macroExpand (AST ast) = 
      
  
-- TYPES 

mkFunType :: Expr -> Expr -> EvalM Expr
mkFunType (Type t1) (Type t2) = 
  pure $ Type (NormArr t1 t2)
mkFunType _ _ = lift $ throwError "bad args to →: expected types"
mlsFunType = liftFun2 mkFunType (NormArr (NormUniv 0) (NormArr (NormUniv 0) (NormUniv 0)))

mkTupleType :: Expr -> Expr -> EvalM Expr
mkTupleType (Type t1) (Type t2) = 
  pure $ Type $ NormSig [("_1", t1), ("_2", t2)]
mkTupleType _ _ = lift $ throwError "bad args to *: expected types"
mlsMkTupleType = liftFun2 mkTupleType (NormArr (NormUniv 0) (NormArr (NormUniv 0) (NormUniv 0)))

-- TUPLES
mkTuple :: Expr -> Expr -> Expr -> Expr -> EvalM Expr
mkTuple _ _ e1 e2 = 
  pure $ Module (Map.fromList [("_1", e1), ("_2", e2)])
mlsMkTuple = liftFun4 mkTuple (NormImplDep "a" (NormUniv 0)
                                 (NormImplDep "b" (NormUniv 0)
                                  (NormArr (Neu (NeuVar "a"))
                                   (NormArr (Neu (NeuVar "b"))
                                    (NormSig [("_1", Neu (NeuVar "a")), ("_2", Neu (NeuVar "b"))])))))
             

-- CONSTRAINTS
doConstrain :: Expr -> Expr -> EvalM Expr
doConstrain (Module mod) (Type (NormSig sig)) = 
  case constrain mod sig of 
    Just x -> pure $ Module x
    Nothing -> lift $ throwError ("could not constrain structure " <> show mod <> " with signature " <> show sig)
  where
    constrain m ((l, _) : xs) = 
      case Map.lookup l m of 
        Just x -> case (constrain m xs) of
          Just mp -> Just $ Map.insert l x mp
          Nothing -> Nothing
        Nothing -> Nothing
    constrain _ [] = Just Map.empty
doConstrain _ _ = lift $ throwError "bad args to <: expected structure and signature"
mlsConstrain = liftFun2 doConstrain (NormArr Undef (NormArr Undef Undef))

-- subtype
-- doSubtype :: Expr -> Expr -> EvalM Expr
-- doSubtype (Type t1) (Type t2) = 
--   if subtype t1 t2 then pure (PrimE (Bool True)) else pure (PrimE (Bool False))
-- doSubtype _ _ = lift $ throwError "bad args to subtype"
-- mlsSubtype = liftFun2 doSubtype Undef Undef Undef



  
coreStructure :: Map.Map String Expr
coreStructure = Map.fromList [
  -- Types
  ("Int",  Type (NormPrim IntT)),
  ("Bool", Type (NormPrim BoolT)),
  ("Unit", Type (NormPrim UnitT)),
  ("𝒰", Type (NormUniv 0)),
  ("→", mlsFunType),
  ("sig", Special MkSig),
  ("×", mlsMkTupleType),

  -- misc. functions (constructors etc.)
  (",", mlsMkTuple),
  ("<:", mlsConstrain),
  (":", Special Annotate),
  ("|", mlsUpd),
  ("with", mlsWith),

  -- macro stuff
  ("Atom", mlsAtom),
  ("Node", mlsNode),
  ("syntax", Special Mac),
  -- ("macro-expand", (mlsMacroExpand, Undef))
  -- ("subtype", mlsSubtype),
  
  -- language constructs
  (".",           Special Access),
  ("if",          Special If),
  ("do",          Special Do),
  ("seq",         Special Seq),
  ("lambda",      Special Lambda),
  ("quote",       Special MkQuote),
  ("λ",           Special Lambda),
  ("let",         Special Let),
  ("handle",      Special Handle),
  ("handler",     Special MkHandler),
  ("handle-with", Special HandleWith),
  ("structure",   Special MkStructure),
  ("signature",   Special MkSig),
  ("struct",      mlsStruct),
  ("sig",         mlsSig),
  ("match",       Special MkMatch),
  ("open",        Special Open),
  ("let-open",    Special LetOpen),

  ("def",          Special Def),
  ("≜",            Special Def),
  ("defn",         mlsDefun) ,
  ("defsyntax",    mlsDefmac),
  ("defstructure", mlsDefStructure),
  ("defstruct",    mlsDefStruct),
  ("defsignature", mlsDefSig),
  ("effect",       Special MkEffect),
  ("variant",      Special DefVariant)
  -- ("signature", (mlsDefSignature, Undef))
  ]

