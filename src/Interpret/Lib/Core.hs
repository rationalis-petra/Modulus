module Interpret.Lib.Core (coreTerms) where


import qualified Data.Map as Map

import Data
import Syntax.Utils
import Interpret.Eval (liftFun, liftFun2, liftFun3, liftFun4)
import Interpret.EvalM (throwError)

-- import Typecheck.Typecheck2 (subtype)


-- helper functions
get_symlist [] = Just []
get_symlist ((Symbol s) : args) =
  case get_symlist args of
    Just syms -> Just $ s : syms
    Nothing -> Nothing
get_symlist _ = Nothing

get_bindlist :: [Normal] -> Maybe ([String], [Normal])
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
toDefs _ = throwError "error: expected symbol value pair"

  
  -- MACROS
opDot :: [AST] -> EvalM AST
opDot [(Cons (op : xs)), rhs] = 
  pure $ (Cons [op, (Cons xs), rhs])
opDot args =  (throwError $ "bad args to macro: dot " <> show args)
mlsDot = BuiltinMac opDot

defStructure :: [AST] -> EvalM AST
defStructure (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom (Special MkStructure) : bdy)])
defStructure _ = throwError "Bad Number of to macro: module" 
mlsDefStructure = BuiltinMac defStructure

defStruct :: [AST] -> EvalM AST
defStruct (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom mlsStruct : bdy)])
defStruct _ = throwError "Bad Number of to macro: module" 
mlsDefStruct = BuiltinMac defStruct

defSig :: [AST] -> EvalM AST
defSig (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom (Special MkSig) : bdy)])
defSig _ = throwError "Bad Number of to macro: module" 
mlsDefSignature = BuiltinMac defSig

defFun :: [AST] -> EvalM AST
defFun (sym : fncdef) = 
  pure $ (Cons [Atom (Special Def), sym, Cons (Atom (Special Lambda) : fncdef)])
defFun args =  throwError $ "bad args to macro: defn" <> show args
mlsDefun = BuiltinMac defFun

defMac :: [AST] -> EvalM AST
defMac [sym, symlist, bdy] = 
  pure $ Cons [Atom (Special Def), sym, Cons [Atom (Special Mac), symlist, bdy]]
defMac args =  throwError $ "bad args to macro: defsyntax" <> show args
mlsDefmac = BuiltinMac defMac


--- Structures
struct :: [AST] -> EvalM AST
struct bindlist = do
  mldebdy <- toDefs bindlist 
  pure $ Cons (Atom (Special MkStructure) : mldebdy)
mlsStruct = BuiltinMac struct

sig :: [AST] -> EvalM AST
sig bindlist = do
  mldebdy <- toDefs bindlist 
  pure $ Cons (Atom (Special MkSig) : mldebdy)
mlsSig = BuiltinMac sig
      
  
-- TYPES 

-- TODO: to be well formed, these must accept types...
mkTupleType :: Normal -> Normal -> EvalM Normal
mkTupleType t1 t2 = 
  pure $ NormSig [("_1", t1), ("_2", t2)]
mlsMkTupleType = liftFun2 mkTupleType (NormArr (NormUniv 0) (NormArr (NormUniv 0) (NormUniv 0)))

-- TUPLES
mkTuple :: Normal -> Normal -> Normal -> Normal -> EvalM Normal
mkTuple t1 t2 e1 e2 = 
  pure $ NormSct [("_1", (e1, [])), ("_2", (e2, []))] (NormSig [("_1", t1), ("_2", t2)])
mlsMkTuple = liftFun4 mkTuple (NormImplProd "A" (NormUniv 0)
                                 (NormImplProd "B" (NormUniv 0)
                                  (NormArr (mkVar "A")
                                   (NormArr (mkVar "B")
                                    (NormSig [("_1", mkVar "A"), ("_2", mkVar "B")])))))

  
-- CONSTRAINTS

mkPropEqType :: Normal
mkPropEqType = NormImplProd "A" (NormUniv 0) (NormArr (mkVar "A") (NormArr (mkVar "A") (NormUniv 0)))
mkPropEq = liftFun3 f mkPropEqType
  where
    f _ l r = pure $ PropEq l r

mkReflType :: Normal 
mkReflType = NormImplProd "A" (NormUniv 0) (NormProd "a" (mkVar "A")
                                             (PropEq (Neu (NeuVar "a" (mkVar "A")) (mkVar "A")) (Neu (NeuVar "a" (mkVar "A")) (mkVar "A"))))

mkRefl :: Normal
mkRefl = liftFun2 f mkReflType 
  where 
    f _ a = pure $ Refl a

  
coreTerms :: [(String, Normal)]
coreTerms =
  [ ("Bool", PrimType BoolT)
  , ("Unit", PrimType UnitT)
  , ("𝒰",    NormUniv 0)
  , ("→",    Special MkProd)

  -- misc functions
  , ("*", mlsMkTupleType)
  , (",", mlsMkTuple)

  , ("refl", mkRefl)
  , ("≡", mkPropEq)

  -- TODO macro stuff

  -- FFI
  , ("foreign-adapter", Special ForeignAdapter)
  
  -- language constructs
  , (".",           Special Access)
  , (":",           Special Annotate)
  , ("if",          Special If)
  , ("do",          Special Do)
  , ("quote",       Special MkQuote)
  , ("λ",           Special Lambda)
  , ("let",         Special Let)
  , ("structure",   Special MkStructure)
  , ("signature",   Special MkSig)
  , ("struct",      mlsStruct)
  , ("sig",         mlsSig)
  , ("match",       Special MkMatch)
  , ("comatch",     Special MkCoMatch)
  , ("open",        Special Open)
  , ("let-open",    Special LetOpen)

  , ("def",           Special Def)
  , ("≜",             Special Def)
  , ("defn",          mlsDefun)
  , ("def-syntax",    mlsDefmac)
  , ("def-structure", mlsDefStructure)
  , ("def-struct",    mlsDefStruct)
  , ("def-signature", mlsDefSignature)
  , ("induct",        Special Induct)
  , ("coinduct",      Special Coinduct)
  ]

