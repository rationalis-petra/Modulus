{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Core (coreTerms) where

import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError, throwError)

import qualified Data.Map as Map

import Data
import Syntax.Utils
import Interpret.Eval (liftFun, liftFun2, liftFun3, liftFun4)
import Interpret.EvalM

-- import Typecheck.Typecheck2 (subtype)


-- helper functions
get_symlist [] = Just []
get_symlist ((Symbol s) : args) =
  case get_symlist args of
    Just syms -> Just $ s : syms
    Nothing -> Nothing
get_symlist _ = Nothing

get_bindlist :: [Normal m] -> Maybe ([String], [Normal m])
get_bindlist [] = Just ([], [])
get_bindlist ((Symbol s) : val : bindings) =
  case get_bindlist bindings of
    Just (syms, vals) -> Just $ ((s : syms), (val : vals))
    Nothing -> Nothing
get_bindlist _ = Nothing

toDefs :: MonadError String m => [AST m] -> m [AST m]
toDefs (Cons [Atom (Symbol s), val] : tl) = do
  tl' <- toDefs tl
  pure (Cons [Atom (Special Def), Atom (Symbol s), val] : tl')
toDefs [] = pure []
toDefs _ = throwError "error: expected symbol value pair"

  
  -- MACROS
opDot :: MonadError String m => [AST m] -> m (AST m)
opDot [(Cons (op : xs)), rhs] = 
  pure $ (Cons [op, (Cons xs), rhs])
opDot args =  (throwError $ "bad args to macro: dot " <> show args)

mlsDot :: MonadError String m => Normal m
mlsDot = BuiltinMac opDot


defStructure :: MonadError String m => [AST m] -> m (AST m)
defStructure (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom (Special MkStructure) : bdy)])
defStructure _ = throwError "Bad Number of to macro: module" 

mlsDefStructure :: MonadError String m => Normal m
mlsDefStructure = BuiltinMac defStructure


defStruct :: MonadError String m => [AST m] -> m (AST m)
defStruct (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom mlsStruct : bdy)])
defStruct _ = throwError "Bad Number of to macro: module" 

mlsDefStruct :: MonadError String m => Normal m
mlsDefStruct = BuiltinMac defStruct


defSig :: MonadError String m => [AST m] -> m (AST m)
defSig (sym : bdy) = 
  pure $ Cons ([Atom (Special Def), sym, Cons (Atom (Special MkSig) : bdy)])
defSig _ = throwError "Bad Number of to macro: module" 

mlsDefSignature :: MonadError String m => Normal m
mlsDefSignature = BuiltinMac defSig


defFun :: MonadError String m => [AST m] -> m (AST m)
defFun (sym : fncdef) = 
  pure $ (Cons [Atom (Special Def), sym, Cons (Atom (Special Lambda) : fncdef)])
defFun args =  throwError $ "bad args to macro: defn" <> show args

mlsDefn :: MonadError String m => Normal m
mlsDefn = BuiltinMac defFun

defInfix :: MonadError String m => [AST m] -> m (AST m)
defInfix [Cons (sym:args), def] = 
  pure $ Cons [Atom (Special Def), sym, Cons (Atom (Special Lambda) : (Cons args) : [def])]
defInfix [sym, def] = 
  pure $ Cons [Atom (Special Def), sym, def]
defInfix args =  throwError $ "bad args to macro: ≜" <> show args

mlsDefInfix :: MonadError String m => Normal m
mlsDefInfix = BuiltinMac defInfix


defMac :: MonadError String m => [AST m] -> m (AST m)
defMac [sym, symlist, bdy] = 
  pure $ Cons [Atom (Special Def), sym, Cons [Atom (Special Mac), symlist, bdy]]
defMac args =  throwError $ "bad args to macro: defsyntax" <> show args

mlsDefmac :: MonadError String m => Normal m
mlsDefmac = BuiltinMac defMac


--- Structures
struct :: MonadError String m => [AST m] -> m (AST m)
struct bindlist = do
  mldebdy <- toDefs bindlist 
  pure $ Cons (Atom (Special MkStructure) : mldebdy)

mlsStruct :: MonadError String m => Normal m
mlsStruct = BuiltinMac struct

sig :: MonadError String m => [AST m] -> m (AST m)
sig bindlist = do
  mldebdy <- toDefs bindlist 
  pure $ Cons (Atom (Special MkSig) : mldebdy)

mlsSig :: MonadError String m => Normal m
mlsSig = BuiltinMac sig
      
  
-- TYPES 

-- TODO: to be well formed, these must accept types...
mkTupleType :: Applicative m => Normal m -> Normal m -> m (Normal m)
mkTupleType t1 t2 = pure $ NormSig [("_1", t1), ("_2", t2)]

mlsMkTupleType :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsMkTupleType = liftFun2 mkTupleType (NormArr (NormUniv 0) (NormArr (NormUniv 0) (NormUniv 0)))

-- TUPLES
mkTuple :: Applicative m => Normal m -> Normal m -> Normal m -> Normal m -> m (Normal m)
mkTuple t1 t2 e1 e2 = 
  pure $ NormSct [("_1", (e1, [])), ("_2", (e2, []))] (NormSig [("_1", t1), ("_2", t2)])

  
mlsMkTuple :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsMkTuple = liftFun4 mkTuple (NormImplProd "A" (NormUniv 0)
                                 (NormImplProd "B" (NormUniv 0)
                                  (NormArr (mkVar "A")
                                   (NormArr (mkVar "B")
                                    (NormSig [("_1", mkVar "A"), ("_2", mkVar "B")])))))

  
-- CONSTRAINTS

mkPropEqType :: Normal m
mkPropEqType = NormImplProd "A" (NormUniv 0) (NormArr (mkVar "A") (NormArr (mkVar "A") (NormUniv 0)))

mkPropEq :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mkPropEq = liftFun3 f mkPropEqType
  where
    f _ l r = pure $ PropEq l r

mkReflType :: Normal m
mkReflType = NormImplProd "A" (NormUniv 0) (NormProd "a" (mkVar "A")
                                             (PropEq (Neu (NeuVar "a" (mkVar "A")) (mkVar "A")) (Neu (NeuVar "a" (mkVar "A")) (mkVar "A"))))

mkRefl :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mkRefl = liftFun2 f mkReflType 
  where 
    f _ a = pure $ Refl a

  
coreTerms :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Normal m)]
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
  , ("≜",             mlsDefInfix)
  , ("defn",          mlsDefn)
  , ("def-syntax",    mlsDefmac)
  , ("def-structure", mlsDefStructure)
  , ("def-struct",    mlsDefStruct)
  , ("def-signature", mlsDefSignature)
  , ("induct",        Special Induct)
  , ("coinduct",      Special Coinduct)
  ]

