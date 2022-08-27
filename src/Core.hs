{-# LANGUAGE TemplateHaskell #-}
module Core where
import Data

import Data.Text (Text, pack, unpack)
import Data.Vector (Vector)

import Control.Lens hiding (Context)
import Control.Monad.State (State) 
import Control.Monad.Except (ExceptT, Except) 
import Control.Monad.Reader (ReaderT) 

import qualified Data.Map as Map
import qualified Control.Monad.Except as Except 
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State as State

import Syntax.Utils
import Interpret.Transform
import Syntax.TIntermediate

import qualified Interpret.Environment as Env
import qualified Interpret.Type as Type
import qualified Interpret.Transform as Action


type SigDefn = (Map.Map String Normal)


-- "correctly" lifted monadic operations for eval
-- ask = Action.lift $ Reader.ask
-- local :: Environment -> EvalM a -> EvalM a
-- local env m = localF (\_ -> env) m

-- localF :: (Environment -> Environment) -> EvalM a -> EvalM a
-- localF f (ActionMonadT mnd) =
--   ActionMonadT (Reader.local f mnd)
-- throwError err = Action.lift $ Reader.lift $ Except.throwError err


  
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

    -- fromDef (TVariantDef nme params id alts ty) = pure (VariantDef nme params id alts ty)
toTopCore (TExpr v) = TopExpr <$> toCore v


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

toCore (TModule map) = do
  coreDefs <- mapM defToCore map
  pure (CSct coreDefs)
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
      
    defToCore (TOpenDef bdy Nothing) = err "open not typed"
    -- defToCore (TVariantDef nme [String] Int [(String, Int, [Normal])]
    -- defToCore (TEffectDef  nme [String] Int [(String, Int, [Normal])]

  
  -- = SingleDef String Core Normal
  -- | VariantDef String [String] [(String, [Core])] 
  -- | EffectDef  String [String] [(String, [Core])]
  -- | OpenDef Core SigDefn

  
  -- = TVariantDef String [String] Int [(String, Int, [Normal])]
  -- | TEffectDef  String [String] Int [(String, Int, [Normal])]
  -- | TSingleDef  String TIntermediate (Maybe Normal)
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

toCore (TIF cond e1 e2) = do
  cond' <- toCore cond
  e1' <- toCore e1
  e2' <- toCore e2
  pure (CIF cond' e1' e2')

-- toCore x = err ("unimplemented" <> show x)
