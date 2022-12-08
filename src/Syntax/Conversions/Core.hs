{-# LANGUAGE PolyKinds, FlexibleContexts #-}
module Syntax.Conversions.Core where

import Syntax.Normal(Pattern(..),
                     CoPattern(..),
                     Normal(..),
                     Neutral(..),
                     ArgType(..))
import Syntax.Core
import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           IPattern(..),
                           IArg(..))

import Control.Monad.State (State, runState)
import Control.Monad.Except (MonadError, throwError)

import qualified Interpret.Environment as Env
import Syntax.TIntermediate
import Syntax.Utils (typeVal)
  
toTopCore :: MonadError String m => TIntTop n Normal -> m (TopCore n)  
toTopCore (TDefinition def) = TopDef <$> fromDef def
  where
    fromDef (TSingleDef name body (Just ty)) = do
      coreBody <- toCore body
      pure (SingleDef name coreBody ty)
    fromDef (TSingleDef name body Nothing) = throwError "definitions must be typed"

    fromDef (TInstanceDef name typeclass) = do
      pure (InstanceDef name typeclass)

    fromDef (TOpenDef body (Just ty)) = do
      coreBody <- toCore body
      let (NormSig sig) = ty
      pure (OpenDef coreBody sig)
    fromDef (TOpenDef body Nothing) = throwError "definitions must be typed"

    fromDef (TOpenClsDef body) = do
      coreBody <- toCore body
      pure (OpenClsDef coreBody)

    fromDef (TInductDef sym id params ctor alts) = do
      ctorty <- typeVal ctor
      pure (InductDef sym id params ctor ctorty alts)
    fromDef (TCoinductDef sym id params ctor alts) = do
      ctorty <- typeVal ctor
      pure (CoinductDef sym id params ctor ctorty alts)
  
toTopCore (TExpr expr) = TopExpr <$> toCore expr

toTopCore (TAnnotation sym term) = TopAnn sym <$> toCore term


toCore :: MonadError String m => TIntermediate n Normal -> m (Core n)  
toCore (TValue v) = pure (CNorm v)
toCore (TSymbol s) = pure (CVar s)
toCore (TAccess int field) = do
  body <- toCore int
  pure (CDot body field)
toCore (TApply t1 t2) = do
  c1 <- toCore t1
  c2 <- toCore t2
  pure $ CApp c1 c2
toCore (TImplApply t1 t2) = do
  c1 <- toCore t1
  c2 <- toCore t2
  pure $ CApp c1 c2
toCore (TLambda args body lty) = do
  ty <- case lty of 
    Just ty -> pure ty
    Nothing -> throwError "cannot convert untyped lambda to core!"
  mkLambdaTyVal args body ty

  where
    mkLambdaTyVal :: MonadError String m => [(TArg n Normal, ArgType)] -> TIntermediate n Normal -> Normal n -> m (Core n)
    mkLambdaTyVal [] body _ = toCore body
    mkLambdaTyVal (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyVal args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyVal (arg : args) body (NormProd var aty l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormProd var aty l r)
    mkLambdaTyVal _ _ ty = throwError ("mkLambdaTyVal failed: " <> show ty) 


    mkLambdaTyExpr :: MonadError String m => [(TArg n Normal, ArgType)] -> TIntermediate n Normal -> Normal n -> m (Core n)
    mkLambdaTyExpr [] body _ = toCore body
    mkLambdaTyExpr (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyExpr (arg : args) body (NormProd var aty l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormProd var aty l r)

    getVar :: (TArg m ty, ArgType) -> String
    getVar (BoundArg var _, _)  = var
    getVar (InfArg var _  , _)  = var

toCore (TProd (arg, aty) body) = do
  body' <- toCore body 
  case arg of 
    BoundArg var ty -> pure $ CProd var aty (CNorm ty) body'
    TWildCard ty -> case aty of  
      Visible -> pure $ CArr (CNorm ty) body'
      Hidden -> throwError "cannot have hidden arrow!"
      Instance -> throwError "cannot have instance arrow!"
  
  

toCore (TStructure map (Just ty)) = do
  coreDefs <- mapM defToCore map
  pure (CSct coreDefs ty)
  where
    defToCore (TSingleDef nme bdy (Just ty)) = do
      bdy' <- toCore bdy
      pure (SingleDef nme bdy' ty)
    defToCore (TSingleDef nme bdy Nothing) = throwError "definition not typed"
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        NormSig sm -> pure sm
        _ -> throwError "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TInductDef sym id params ctor alts) = do
      ctorty <- typeVal ctor
      pure (InductDef sym id params ctor ctorty alts)

  
  -- | TOpenDef TIntermediate (Maybe Normal)

  
toCore (TSignature map) = do
  coreDefs <- mapM defToCore map
  pure (CSig coreDefs)
  where
    defToCore (TSingleDef nme bdy t) = do
      bdy' <- toCore bdy
      -- TODO: this is bad, make sure to properly check signatures for well-formedness
      --  or, is this done during typechecking??
      -- TypeN is the type of signatures??
      pure (SingleDef nme bdy' (NormUniv 0))
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        NormSig sm -> pure sm
        _ -> throwError "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TOpenDef bdy Nothing) = throwError "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [Normal])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [Normal])]

toCore (TIF cond e1 e2 (Just ty)) = do
  cond' <- toCore cond
  e1' <- toCore e1
  e2' <- toCore e2
  pure (CIf cond' e1' e2' ty)

toCore (TMatch term patterns (Just ty)) = do
  term' <- toCore term
  patterns' <- toCoreCases patterns
  pure $ CMatch term' patterns' ty
  where
    toCoreCases [] = pure []
    toCoreCases ((p, e):ps) = do
      e' <- toCore e
      p' <- toCorePat p
      ps' <- toCoreCases ps
      pure ((p', e') : ps')

    toCorePat :: MonadError String m => TPattern n Normal -> m (Pattern n)
    toCorePat TWildPat = pure WildCard
    toCorePat (TBindPat str (Just ty)) = pure (VarBind str ty)
    toCorePat (TIMatch id1 id2 _ ty pats) = do
      pats' <- mapM toCorePat pats
      pure $ (MatchInduct id1 id2 pats')
    toCorePat (TBuiltinMatch fn _ ty pats) = do
      pats' <- mapM toCorePat pats
      pure $ InbuiltMatch (fn pats')

  
toCore (TCoMatch patterns (Just ty)) = do
  patterns' <- toCoreCases patterns
  pure $ CCoMatch patterns' ty
  where
    toCoreCases [] = pure []
    toCoreCases ((p, e):ps) = do
      e' <- toCore e
      p' <- toCorePat p
      ps' <- toCoreCases ps
      pure ((p', e') : ps')

    toCorePat :: MonadError String m => TCoPattern n Normal -> m (CoPattern n)
    toCorePat TCoWildPat = pure CoWildCard
    toCorePat (TCoBindPat str (Just ty)) = pure (CoVarBind str ty)
    toCorePat (TCoinductPat name id1 id2 _ ty pats) = do
      pats' <- mapM toCorePat pats
      pure $ (CoMatchInduct name id1 id2 pats')


toCore (TAdaptForeign lang lib imports (Just ty)) =
  pure $ CAdaptForeign lang lib imports
toCore x = throwError ("toCore: unimplemented for " <> show x)
