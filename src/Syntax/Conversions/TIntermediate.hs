module Syntax.Conversions.TIntermediate where

import Data(EvalM,
            TopCore(..),
            Core (..),
            Pattern(..),
            InbuiltCtor(..),
            Definition(..),
            Normal,
            Normal'(..),
            Neutral,
            Neutral'(..))
import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           IPattern(..),
                           ICoPattern(..),
                           IArg(..))

import Interpret.EvalM (local, fresh_id, fresh_var, throwError)
import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, Except, runExceptT, runExcept)
import qualified Control.Monad.Except as Except

import qualified Interpret.Environment as Env
import qualified Interpret.Eval as Eval
import Syntax.TIntermediate


toTIntermediateTop :: Intermediate -> EvalM (TIntTop TIntermediate')
toTIntermediateTop (IDefinition def) = TDefinition <$> toTDef def
toTIntermediateTop (IAnnotation str bdy) = TAnnotation str <$> toTIntermediate bdy
toTIntermediateTop i = TExpr <$> toTIntermediate i

-- TODO: make sure to update the context with typeLookup
toTIntermediate :: Intermediate -> EvalM (TIntermediate TIntermediate')
toTIntermediate (IValue expr) = pure (TValue expr)
toTIntermediate (ISymbol s) = pure (TSymbol s)
toTIntermediate (IAccess i s) = do
  t <- toTIntermediate i
  pure (TAccess t s)


-- Note: implicit argument resolution done during type-checking!
toTIntermediate (IApply i1 i2) = do
  i1' <- toTIntermediate i1
  i2' <- toTIntermediate i2
  pure (TApply i1' i2')

toTIntermediate (IImplApply i1 i2) = do
  i1' <- toTIntermediate i1
  i2' <- toTIntermediate i2
  pure (TImplApply i1' i2')

toTIntermediate (ILambda args bdy) = do
  args' <- processArgs args
  bdy' <- toTIntermediate bdy
  pure $ TLambda args' bdy' Nothing
  where
    processArgs :: [(IArg, Bool)] -> EvalM [(TArg TIntermediate', Bool)]
    processArgs [] = pure []
    processArgs ((Sym s, b) : xs) =
      if b then  do
        tl <- processArgs xs
        pure $ ((BoundArg s (TIntermediate' $ TValue $ NormUniv 0), b) : tl)
      else do
        tl <- processArgs xs
        var <- fresh_var
        pure $ (InfArg s var, b) : tl
    processArgs ((Annotation s i, b) : xs) = do
      ty <- toTIntermediate i
      tl <- processArgs xs
      pure ((BoundArg s (TIntermediate' ty), b) : tl)

  

toTIntermediate (IProd arg bdy) = do
  arg' <- case arg of
    (Sym var, bl) ->
      throwError "cannot place sym arg in dependent product"
    (Annotation var ty, bl) -> do
      ty' <- toTIntermediate ty
      pure (BoundArg var (TIntermediate' ty'), bl)
    (IWildCardArg ty, bl) ->  do
      ty' <- toTIntermediate ty
      pure (TWildCard (TIntermediate' ty'), bl)
  body' <- toTIntermediate bdy
  pure $ TProd arg' body'


toTIntermediate (IStructure defList) = TStructure <$> mapM toTDef defList <*> pure Nothing
toTIntermediate (ISignature defList) = TSignature <$> mapM toTDef defList
  
toTIntermediate (IIF cond e1 e2) = do
  cond' <- toTIntermediate cond 
  e1' <- toTIntermediate e1 
  e2' <- toTIntermediate e2
  pure (TIF cond' e1' e2' Nothing)

toTIntermediate (IMatch e1 cases) = do 
  e1' <- toTIntermediate e1 
  cases' <- mapM toCase cases 
  pure (TMatch e1' cases' Nothing)

  where
    toCase :: (IPattern, Intermediate) -> EvalM (TPattern TIntermediate', TIntermediate TIntermediate')
    toCase (ipat, e) = do 
      tpat <- toTPat ipat 
      e' <- toTIntermediate e 
      pure (tpat, e')

    toTPat :: IPattern -> EvalM (TPattern TIntermediate')
    toTPat IWildCard = pure TWildPat
    toTPat (ISingPattern s) = pure (TBindPat s Nothing)
    toTPat (ICheckPattern pat subPatterns) = do
      subPatterns' <- mapM toTPat subPatterns
      extractPattern pat subPatterns'

    extractPattern expr subPatterns = do
      val <- toTIntermediate expr
      case val of 
        TValue (NormIVal name altid vid strip [] ty) ->
          pure (TIMatch altid vid strip (TIntermediate' (TValue ty)) subPatterns)
        TValue (InbuiltCtor ctor) -> case ctor of
          IndPat _ matcher n _ ty -> pure $ TBuiltinMatch matcher n (TIntermediate' (TValue ty)) subPatterns
        _ -> throwError ("couldn't extract pattern from val: " <> show val)

  
toTIntermediate (ICoMatch cases) = do 
  cases' <- mapM toCase cases 
  pure (TCoMatch cases' Nothing)

  where
    toCase :: (ICoPattern, Intermediate) -> EvalM (TCoPattern TIntermediate', TIntermediate TIntermediate')
    toCase (ipat, e) = do 
      tpat <- toTPat ipat 
      e' <- toTIntermediate e 
      pure (tpat, e')

    toTPat :: ICoPattern -> EvalM (TCoPattern TIntermediate')
    toTPat ICoWildCard = pure TCoWildPat
    toTPat (ICoSingPattern s) = pure (TCoBindPat s Nothing)
    toTPat (ICoCheckPattern pat subPatterns) = do
      subPatterns' <- mapM toTPat subPatterns
      extractPattern pat subPatterns'

    extractPattern :: Intermediate
                   -> [TCoPattern TIntermediate'] -> EvalM (TCoPattern TIntermediate')
    extractPattern expr subPatterns = do
      val <- toTIntermediate expr
      case val of 
        TValue (NormCoDtor name altid vid len strip terms ty) ->
          pure (TCoinductPat name altid vid strip (TIntermediate' (TValue ty)) subPatterns)
        _ -> throwError ("couldn't extract pattern from val: " <> show val)

toTIntermediate (IDefinition _) = throwError ("defs must be toplevel! ")
toTIntermediate x = throwError ("toTIntermediate not implemented for: "  <> show x)


toTDef :: IDefinition -> EvalM (TDefinition TIntermediate')
toTDef (ISingleDef s i mann) = do
  t <- toTIntermediate i
  ann' <- case mann of
    Just ann -> Just . TIntermediate' <$> toTIntermediate ann
    Nothing -> pure Nothing
  pure (TSingleDef s t ann')

toTDef (IOpenDef i) = do
  t <- toTIntermediate i
  pure (TOpenDef t Nothing)

toTDef (IInductDef sym params ty alts) = do
  params' <- processParams params
  ty' <- toTIntermediate ty
  alts' <- processAlts alts
  id <- fresh_id
  pure $ TInductDef sym id params' (TIntermediate' ty') alts'
  where
    processAlts :: [(String, Intermediate)] -> EvalM [(String, Int, TIntermediate')] 
    processAlts [] = pure []
    processAlts ((str, inter) : params) = do
      tint' <- toTIntermediate inter
      id <- fresh_id
      rest <- processAlts params
      pure $ ((str, id, (TIntermediate' tint')) : rest)

    processParams :: [IArg] -> EvalM [(String, TIntermediate')]
    processParams [] = pure []
    processParams (Sym sym : args) = do
      args' <- processParams args
      pure $ ((sym, TIntermediate' (TValue (NormUniv 0))) : args')

    processParams (Annotation sym inter : args) = do
      args' <- processParams args
      inter' <- toTIntermediate inter
      pure $ ((sym, TIntermediate' inter') : args')

    processParams (IWildCardArg inter : args) = do
      throwError "inductive definitions do not accept wildcard parameters"

toTDef (ICoinductDef sym params ty alts) = do
  params' <- processParams params
  ty' <- toTIntermediate ty
  alts' <- processAlts alts
  id <- fresh_id
  pure $ TCoinductDef sym id params' (TIntermediate' ty') alts'
  where
    processAlts :: [(String, Intermediate)] -> EvalM [(String, Int, TIntermediate')] 
    processAlts [] = pure []
    processAlts ((str, inter) : params) = do
      tint' <- toTIntermediate inter
      id <- fresh_id
      rest <- processAlts params
      pure $ ((str, id, (TIntermediate' tint')) : rest)

    processParams :: [IArg] -> EvalM [(String, TIntermediate')]
    processParams [] = pure []
    processParams (Sym sym : args) = do
      args' <- processParams args
      pure $ ((sym, TIntermediate' (TValue (NormUniv 0))) : args')

    processParams (Annotation sym inter : args) = do
      args' <- processParams args
      inter' <- toTIntermediate inter
      pure $ ((sym, TIntermediate' inter') : args')

    processParams (IWildCardArg inter : args) = do
      throwError "inductive definitions do not accept wildcard parameters"
