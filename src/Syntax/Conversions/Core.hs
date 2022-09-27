module Syntax.Conversions.Core where

import Data(EvalM,
            TopCore(..),
            Core (..),
            Pattern(..),
            CoPattern(..),
            Definition(..),
            Normal,
            Normal'(..),
            Neutral,
            Neutral'(..))
import Syntax.Intermediate(Intermediate(..),
                           IDefinition(..),
                           IPattern(..),
                           IArg(..))

import Interpret.EvalM (local, fresh_id, fresh_var, throwError)
import Control.Monad.State (State, runState)
import Control.Monad.Except (ExceptT, Except, runExceptT, runExcept)
import qualified Control.Monad.Except as Except

import qualified Interpret.Environment as Env
import qualified Typecheck.Context as Ctx 
import Syntax.TIntermediate
import qualified Interpret.Eval as Eval

err = Except.throwError
  
toTopCore :: TIntTop Normal -> Except String TopCore  
toTopCore (TDefinition def) = TopDef <$> fromDef def
  where
    fromDef (TSingleDef name body (Just ty)) = do
      coreBody <- toCore body
      pure (SingleDef name coreBody ty)
    fromDef (TSingleDef name body Nothing) = err "definitions must be typed"

    fromDef (TOpenDef body (Just ty)) = do
      coreBody <- toCore body
      let (NormSig sig) = ty
      pure (OpenDef coreBody sig)
    fromDef (TOpenDef body Nothing) = err "definitions must be typed"

    fromDef (TInductDef sym id params ty alts) =
      pure (InductDef sym id params ty alts)
    fromDef (TCoinductDef sym id params ty alts) =
      pure (CoinductDef sym id params ty alts)
toTopCore (TExpr expr) = TopExpr <$> toCore expr
toTopCore (TAnnotation sym term) = TopAnn sym <$> toCore term


toCore :: TIntermediate Normal -> Except String Core  
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
    Nothing -> err "cannot convert untyped lambda to core!"
  mkLambdaTyVal args body ty

  where
    mkLambdaTyVal :: [(TArg Normal, Bool)] -> TIntermediate Normal -> Normal -> Except String Core
    mkLambdaTyVal [] body _ = toCore body
    mkLambdaTyVal (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyVal args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyVal (arg : args) body (NormProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormProd var l r)
    mkLambdaTyVal (arg : args) body (NormImplProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormImplProd var l r)
    mkLambdaTyVal _ _ ty = err ("mkLambdaTyVal failed: " <> show ty) 


    mkLambdaTyExpr :: [(TArg Normal, Bool)] -> TIntermediate Normal -> Normal -> Except String Core
    mkLambdaTyExpr [] body _ = toCore body
    mkLambdaTyExpr (arg : args) body (NormArr l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormArr l r)
    mkLambdaTyExpr (arg : args) body (NormProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormProd var l r)
    mkLambdaTyExpr (arg : args) body (NormImplProd var l r) = do
      let arg' = getVar arg
      body' <- mkLambdaTyExpr args body r
      pure $ CAbs arg' body' (NormImplProd var l r)

    getVar :: (TArg ty, Bool) -> String
    getVar (BoundArg var _, _)  = var
    getVar (InfArg var _  , _)  = var

toCore (TProd (arg, bl) body) = do
  body' <- toCore body 
  case arg of 
    BoundArg var ty ->
      if bl then 
        pure $ CImplProd var (CNorm ty) body'
      else
        pure $ CProd var (CNorm ty) body'
    TWildCard ty ->
      if bl then
        err "cannot have implicit arrow!"
      else
        pure $ CArr (CNorm ty) body'
  
  

toCore (TStructure map (Just ty)) = do
  coreDefs <- mapM defToCore map
  pure (CSct coreDefs ty)
  where
    defToCore (TSingleDef nme bdy (Just ty)) = do
      bdy' <- toCore bdy
      pure (SingleDef nme bdy' ty)
    defToCore (TSingleDef nme bdy Nothing) = err "definition not typed"
    defToCore (TOpenDef bdy (Just ty)) = do
      sig <- case ty of 
        NormSig sm -> pure sm
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TInductDef sym id params ty alts) = 
      pure (InductDef sym id params ty alts)

  
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
        _ -> err "open provided with non-module!"
      bdy' <- toCore bdy
      pure (OpenDef bdy' sig)
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
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

    toCorePat :: TPattern Normal -> Except String Pattern
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

    toCorePat :: TCoPattern Normal -> Except String CoPattern
    toCorePat TCoWildPat = pure CoWildCard
    toCorePat (TCoBindPat str (Just ty)) = pure (CoVarBind str ty)
    toCorePat (TCoinductPat name id1 id2 _ ty pats) = do
      pats' <- mapM toCorePat pats
      pure $ (CoMatchInduct name id1 id2 pats')


toCore x = err ("toCore: unimplemented for " <> show x)
