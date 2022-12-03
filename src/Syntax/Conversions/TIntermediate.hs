{-# LANGUAGE FlexibleContexts #-}

module Syntax.Conversions.TIntermediate where

import Syntax.Normal (Pattern(..),
                      InbuiltCtor(..),
                      Normal(..),
                      Neutral(..),
                      ArgType(Visible, Hidden, Instance),
                      ProgState)
import Syntax.Core(Core (..), TopCore(..), Definition(..))
import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           IPattern(..),
                           ICoPattern(..),
                           IArg(..))

import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Interpret.EvalM (freshIVar, freshID)
import Syntax.TIntermediate


toTIntermediateTop :: (MonadState (ProgState m) m, MonadError String m) => Intermediate m -> m (TIntTop m TIntermediate')
toTIntermediateTop (IDefinition def) = TDefinition <$> toTDef def
toTIntermediateTop (IAnnotation str bdy) = TAnnotation str <$> toTIntermediate bdy
toTIntermediateTop i = TExpr <$> toTIntermediate i

-- TODO: make sure to update the context with typeLookup
toTIntermediate :: (MonadState (ProgState m) m, MonadError String m) => Intermediate m -> m (TIntermediate m TIntermediate')
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
    processArgs :: (MonadState (ProgState m) m, MonadError String m) => [(IArg m, ArgType)] -> m [(TArg m TIntermediate', ArgType)]
    processArgs [] = pure []
    processArgs ((Sym s, aty) : xs) = case aty of 
      Visible -> do
        tl <- processArgs xs
        var <- freshIVar
        pure $ (InfArg s var, aty) : tl
      Hidden -> do
        tl <- processArgs xs
        pure $ ((BoundArg s (TIntermediate' $ TValue $ NormUniv 0), aty) : tl)
      Instance -> throwError "instance args must be annotated"
    processArgs ((Annotation s i, aty) : xs) = do
      ty <- toTIntermediate i
      tl <- processArgs xs
      pure ((BoundArg s (TIntermediate' ty), aty) : tl)

  

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
    toCase :: (MonadState (ProgState m) m, MonadError String m) => (IPattern m, Intermediate m) -> m (TPattern m TIntermediate', TIntermediate m TIntermediate')
    toCase (ipat, e) = do 
      tpat <- toTPat ipat 
      e' <- toTIntermediate e 
      pure (tpat, e')

    toTPat :: (MonadState (ProgState m) m, MonadError String m) => IPattern m -> m (TPattern m TIntermediate')
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
    toCase :: (MonadState (ProgState m) m, MonadError String m) => (ICoPattern m, Intermediate m) -> m (TCoPattern m TIntermediate', TIntermediate m TIntermediate')
    toCase (ipat, e) = do 
      tpat <- toTPat ipat 
      e' <- toTIntermediate e 
      pure (tpat, e')

    toTPat :: (MonadState (ProgState m) m, MonadError String m) => ICoPattern m -> m (TCoPattern m TIntermediate')
    toTPat ICoWildCard = pure TCoWildPat
    toTPat (ICoSingPattern s) = pure (TCoBindPat s Nothing)
    toTPat (ICoCheckPattern pat subPatterns) = do
      subPatterns' <- mapM toTPat subPatterns
      extractPattern pat subPatterns'

    extractPattern :: (MonadState (ProgState m) m, MonadError String m) => Intermediate m -> [TCoPattern m TIntermediate'] -> m (TCoPattern m TIntermediate')
    extractPattern expr subPatterns = do
      val <- toTIntermediate expr
      case val of 
        TValue (NormCoDtor name altid vid len strip terms ty) ->
          pure (TCoinductPat name altid vid strip (TIntermediate' (TValue ty)) subPatterns)
        _ -> throwError ("couldn't extract pattern from val: " <> show val)

toTIntermediate (IAdaptForeign lang lib annotations) = do 
  annotations' <- mapM (\(s1, s2, i) -> (,,) s1 s2 .  TIntermediate' <$> toTIntermediate i) annotations
  pure $ TAdaptForeign lang lib annotations' Nothing

toTIntermediate (IDefinition _) = throwError ("defs must be toplevel! ")
toTIntermediate x = throwError ("toTIntermediate not implemented for: "  <> show x)


toTDef :: (MonadState (ProgState m) m, MonadError String m) => IDefinition m -> m (TDefinition m TIntermediate')
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
  id <- freshID
  pure $ TInductDef sym id params' (TIntermediate' ty') alts'
  where
    processAlts :: (MonadState (ProgState m) m, MonadError String m) => [(String, Intermediate m)] -> m [(String, Int, TIntermediate' m)] 
    processAlts [] = pure []
    processAlts ((str, inter) : params) = do
      tint' <- toTIntermediate inter
      id <- freshID
      rest <- processAlts params
      pure $ ((str, id, (TIntermediate' tint')) : rest)

    processParams :: (MonadState (ProgState m) m, MonadError String m) => [IArg m] -> m [(String, TIntermediate' m)]
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
  id <- freshID
  pure $ TCoinductDef sym id params' (TIntermediate' ty') alts'
  where
    processAlts :: (MonadState (ProgState m) m, MonadError String m) => [(String, Intermediate m)] -> m [(String, Int, TIntermediate' m)] 
    processAlts [] = pure []
    processAlts ((str, inter) : params) = do
      tint' <- toTIntermediate inter
      id <- freshID
      rest <- processAlts params
      pure $ ((str, id, (TIntermediate' tint')) : rest)

    processParams :: (MonadState (ProgState m) m, MonadError String m) => [IArg m] -> m [(String, TIntermediate' m)]
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
