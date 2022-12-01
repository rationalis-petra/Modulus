{-# LANGUAGE FlexibleContexts #-}
module Typecheck.Typecheck where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState)
import Control.Monad.Reader (MonadReader, local)

import Syntax.Normal (PrimType(..),
                      Normal(..),
                      Neutral(..),
                      ArgType(..),
                      Environment,
                      ProgState,
                      var_counter)
import Syntax.Core(Core(..))
import Syntax.TIntermediate


import qualified Interpret.Environment as Env
import qualified Syntax.Conversions as Conv 
import Interpret.EvalM
import qualified Interpret.Eval as Eval
import Syntax.Utils (tyHead, tyTail, typeVal, free, getField, mkVar)

import Typecheck.Constrain


typeCheckTop :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => TIntTop m TIntermediate' -> Environment m
             -> m (Either (TIntTop m Normal, Normal m) (TIntTop m Normal))
typeCheckTop (TExpr e) ctx = do
      (expr, ty, subst) <-  typeCheck e ctx
      -- (expr', ty') <- buildDepFn expr ty
      pure $ Left $ (TExpr expr, ty)
typeCheckTop (TAnnotation sym bdy) ctx = do
      (bdy', ty, subst) <- typeCheck bdy ctx
      pure $ Right $ (TAnnotation sym bdy')
typeCheckTop (TDefinition def) ctx = 
  case def of 
    TSingleDef name expr Nothing -> do
      recTy <- freshVar
      (expr', ty, vsubst) <- typeCheck expr
          (Env.insert name (Neu (NeuVar name recTy) recTy) recTy ctx)
      (_, app, csubst) <- constrain recTy ty ctx
      let (fnlSubstl, fnlSubstr) = rmSubst (show recTy) csubst
      ty' <- tyApp ty app
      if (null fnlSubstl && null fnlSubstr) then 
          pure $ Right $ TDefinition $ TSingleDef name expr' (Just ty')
        else do
          throwError ("subst strings non empty at toplevel: " <> show (fnlSubstl, fnlSubstr))

    TSingleDef name expr (Just (TIntermediate' ty)) -> do
      ty' <- evalTIntermediate ty ctx
      (expr', ty', _) <- case expr of
        TLambda args body Nothing -> 
          typeCheck (TLambda args body (Just (TIntermediate' ty)))
            (Env.insert name (Neu (NeuVar name ty') ty') ty' ctx)
        _ ->
          typeCheck expr (Env.insert name (Neu (NeuVar name ty') ty') ty' ctx)
      pure $ Right $ TDefinition $ TSingleDef name expr' (Just ty')


    TOpenDef expr Nothing -> do 
      (expr', ty, subst) <- typeCheck expr ctx
      if subst /= nosubst
        then 
          throwError "subst non-empty at toplevel!"
        else
          pure $ Right $ TDefinition $ TOpenDef expr' (Just ty)

    TInductDef sym id params (TIntermediate' ty) alts -> do
      -- TODO: check alternative definitions are well-formed (positive, return
      -- correct Constructor) 
      ty' <- evalTIntermediate ty ctx
      index <- readIndex ty'
      (ctx', params') <- updateFromParams params ctx
      (indCtor, indTy) <- mkIndexTy params' index ty' id
      alts' <- processAlts alts params' (Env.insert sym indCtor indTy ctx')
      pure $ Right $ TDefinition $ TInductDef sym id params' indCtor alts'

      where
        processAlts :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Int, TIntermediate' m)] -> [(String, Normal m)] -> Environment m
                    -> m [(String, Int, Normal m)]
        processAlts [] params ctx = pure []
        processAlts ((sym, id, (TIntermediate' ty)) : alts) ps ctx = do
          -- TODO: check for well-formedness!!
          -- TODO: positivity check
          ty' <- evalTIntermediate ty ctx
          alts' <- processAlts alts ps ctx
          pure $ (sym, id, (captureParams ps ty')) : alts'
          where
            captureParams [] ty = ty
            captureParams ((sym, ty) : ps) tl = NormProd sym Hidden ty (captureParams ps tl)

        updateFromParams :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, TIntermediate' m)] -> Environment m -> m (Environment m, [(String, Normal m)])
        updateFromParams [] ctx = pure (ctx, [])
        updateFromParams ((sym, TIntermediate' ty) : args) ctx = do
          ty' <- evalTIntermediate ty ctx
          (ctx', args') <- updateFromParams args
                             (Env.insert sym (Neu (NeuVar sym ty') ty') ty' ctx)
          pure (Env.insert sym (Neu (NeuVar sym ty') ty') ty' ctx', ((sym, ty') : args'))

        readIndex :: (MonadState (ProgState m) m, MonadError String m) => Normal m -> m [(String, Normal m)]
        readIndex (NormUniv n) = pure []
        readIndex (NormProd sym Visible a b) = do 
          tl  <- readIndex b
          pure ((sym, a) : tl)
        readIndex (NormArr a b) = do
          id <- freshVar
          tl  <- readIndex b
          pure ((show id, a) : tl)
        readIndex _ = throwError "bad inductive type annotation"

        -- take first the parameters, then and the index, along with the index's type.  
        -- return a constructor for the type, and the type of the constructor
        mkIndexTy :: Monad m => [(String, Normal m)] -> [(String, Normal m)] -> Normal m -> Int -> m (Normal m, Normal m)
        mkIndexTy params index ty id = mkIndexTy' params index (ty, id) []

        mkIndexTy' :: Monad m => [(String, Normal m)] -> [(String, Normal m)] -> (Normal m, Int) -> [(String, Normal m)] -> m (Normal m, Normal m) 
        mkIndexTy' [] [] (ty, id) args = do 
          pure (NormIType sym id (reverse (map (\(var, ty) -> Neu (NeuVar var ty) ty) args)), ty)

        mkIndexTy' ((sym, ty) : params) index body args = do
          (ctor, ctorty) <- mkIndexTy' params index body ((sym, ty) : args)
          let fty = NormProd sym Visible ty ctorty
          pure $ (NormAbs sym ctor fty, fty)

        mkIndexTy' [] ((sym, ty) : ids) index args = do
          (ctor, ctorty) <- mkIndexTy' [] ids index ((sym, ty) : args)
          pure $ (NormAbs sym ctor ctorty, ctorty)

  
    TCoinductDef sym id params (TIntermediate' ty) alts -> do
      -- TODO: check alternative definitions are well-formed (positive, return
      -- correct Constructor) 
      ty' <- evalTIntermediate ty ctx
      index <- readIndex ty'
      (ctx', params') <- updateFromParams params ctx
      (indCtor, indTy) <- mkIndexTy params' index ty' id
      alts' <- processAlts alts params' (Env.insert sym indCtor indTy ctx')
      pure $ Right $ TDefinition $ TCoinductDef sym id params' indCtor alts'

      where
        processAlts :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) =>
                       [(String, Int, TIntermediate' m)] -> [(String, Normal m)] -> Environment m
                       -> m [(String, Int, Normal m)]
        processAlts [] params ctx = pure []
        processAlts ((sym, id, (TIntermediate' ty)) : alts) ps ctx = do
          -- TODO: check for well-formedness!!
          -- TODO: positivity check
          ty' <- evalTIntermediate ty ctx
          alts' <- processAlts alts ps ctx
          pure $ (sym, id, (captureParams ps ty')) : alts'
          where
            captureParams [] ty = ty
            captureParams ((sym, ty) : ps) tl = NormProd sym Hidden ty (captureParams ps tl)

        updateFromParams :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, TIntermediate' m)] -> Environment m -> m (Environment m, [(String, Normal m)])
        updateFromParams [] ctx = pure (ctx, [])
        updateFromParams ((sym, TIntermediate' ty) : args) ctx = do
          ty' <- evalTIntermediate ty ctx
          (ctx', args') <- updateFromParams args
                             (Env.insert sym (Neu (NeuVar sym ty') ty') ty' ctx)
          pure (Env.insert sym (Neu (NeuVar sym ty') ty') ty' ctx', ((sym, ty') : args'))

        readIndex :: (MonadState (ProgState m) m, MonadError String m) => Normal m -> m [(String, Normal m)]
        readIndex (NormUniv n) = pure []
        readIndex (NormProd sym Visible a b) = do 
          tl  <- readIndex b
          pure ((sym, a) : tl)
        readIndex (NormArr a b) = do
          id <- freshVar
          tl  <- readIndex b
          pure ((show id, a) : tl)
        readIndex _ = throwError "bad inductive type annotation"

        -- take first the parameters, then and the index, along with the index's type.  
        -- return a constructor for the type, and the type of the constructor
        mkIndexTy :: Monad m => [(String, Normal m)] -> [(String, Normal m)] -> Normal m -> Int -> m (Normal m, Normal m)
        mkIndexTy params index ty id = mkIndexTy' params index (ty, id) []

        mkIndexTy' :: Monad m => [(String, Normal m)] -> [(String, Normal m)] -> (Normal m, Int) -> [(String, Normal m)] -> m (Normal m, Normal m) 
        mkIndexTy' [] [] (ty, id) args = do 
          pure (NormIType sym id (reverse (map (\(var, ty) -> Neu (NeuVar var ty) ty) args)), ty)
        mkIndexTy' ((sym, ty) : params) index body args = do
          (ctor, ctorty) <- mkIndexTy' params index body ((sym, ty) : args)
          let fty = NormProd sym Visible ty ctorty
          pure $ (NormAbs sym ctor fty, fty)
        mkIndexTy' [] ((sym, ty) : ids) index args = do
          (ctor, ctorty) <- mkIndexTy' [] ids index ((sym, ty) : args)
          pure $ (NormAbs sym ctor ctorty, ctorty)
          

typeCheck :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => TIntermediate m TIntermediate' -> Environment m -> m (TIntermediate m Normal, Normal m, Subst m)
typeCheck expr env = case expr of
  (TValue v) -> do
    t <- typeVal v
    pure (TValue v, t, nosubst)

  (TSymbol s) -> do
    (_, ty) <- (Env.lookup s env)
    pure (TSymbol s, ty, nosubst)
  
  (TImplApply l r) -> do 
    (l', tl, substl) <- typeCheck l env
    (r', tr, substr) <- typeCheck r env
    substboth <- compose substl substr
    case tl of  
      NormProd var Hidden t1 t2 -> do
        (lapp, rapp, substcomb) <- constrain t1 tr env
        subst <- compose substcomb substboth
        appTy <- evalNIntermediate r' env
        retTy <- Eval.normSubst (appTy, var) t2
        pure (TImplApply l' r', retTy, subst)
      t -> throwError ("implicit application to non-implicit type" <> show t)

  (TApply l r) -> do 
    (l', tl, substl) <- typeCheck l env
    (r', tr, substr) <- typeCheck r env
    substboth <- compose substl substr
    case tl of  
      NormArr t1 t2 -> do 
        (_, app, substcomb) <- constrain t1 tr env
        let r'' = mkApp r' app
        subst <- compose substcomb substboth
        pure (TApply l' r'', t2, subst)
      NormProd var Visible a t2 -> do 
        (_, app, substcomb) <- constrain a tr env
        subst <- compose substcomb substboth
        depApp <- evalNIntermediate r' env
        let r'' = mkApp r' app -- TODO: use depApp instead of r'?? (possibly just an optimisation?)
        retTy <- Eval.normSubst (depApp, var) t2
        pure (TApply l' r'', retTy, subst)
      _ -> do
        (args, unbound, subst, rettype) <- deriveFn tl tr r'
        let (fnl_expr, fnl_ty) = mkFnlFn (reverse args) unbound l' rettype
        subst_fnl <- compose subst substboth
        pure (fnl_expr, fnl_ty, subst_fnl)
        
    where
      -- deriveFn will take the type of the LHS of the apply, and the RHS of the
      -- apply and it's type, and deduce a list of arguments (and unbound types)
      -- from which a new term can be constructed that contains the necessary
      -- implicit application/function abstractions
      -- for example, if we had a function f : {a} -> {b} -> a -> b -> (a × b) in
      -- application f 2, deriveFn would return [int, b, 2], ["b"]

      -- mkFnlFn is simply the function which constructs a term of appropriate
      -- type given the output from deriveFn. In the above example, it would
      -- take as input [int, b, 2], ["b"] (along with the function f, and 
      -- construct the term (λ {b} [x : b] (f {int} {b} 2 x)), which has type
      -- {b} -> b -> (int × b) 


                  -- lhs/ty  rhs/ty     rhs
      -- deriveFn :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) =>
      --             Normal m -> Normal m -> TIntermediate m Normal -> m ([(Bool, TIntermediate m Normal)], [(Normal m, String)], Subst m, Normal m)
      deriveFn (NormProd var Hidden a t2) tr r = do
        (args, unbnd, subst, rettype) <- deriveFn t2 tr r
        case findStrSubst var subst of 
          Just val -> do
            val' <- inferVar val a env
            retTy <- Eval.normSubst (val', var) rettype
            pure (((True, (TValue val')) : args),
                           unbnd,
                           rmSubst var subst,
                           retTy)
          Nothing -> pure ((True, TValue (mkVar var)) : args, ((NormUniv 0, var):unbnd),
                           rmSubst var subst, rettype)
      deriveFn (NormArr t1 t2) tr r = do
        (app, lapp, subst) <- constrain tr t1 env
        pure ([(False, mkApp r app)], [], subst, t2)
      deriveFn t tr r = do
        var' <- freshVar 
        (lapp, rapp, subst) <- constrain (NormArr tr var') t env
        -- TODO
        -- if not (null lapp && null rapp) then err "unsure of how to handle non-empty l/rapp in deriveFn"
        -- else
        pure ([(False, r)], [], subst, var')

      mkFnlFn :: [(Bool, TIntermediate m Normal)] -> [(Normal m, String)] -> TIntermediate m Normal -> Normal m
              -> (TIntermediate m Normal, Normal m)
      mkFnlFn args unbound bdy bodyty = (fnlfn, fnlty)
        where
          --fnlfn :: TIntermediate m Normal
          fnlfn = if (null args)
            then
              (mkbdy [] bdy)
            else
              TLambda (map (\(ty, s) -> (BoundArg s ty, Hidden)) unbound) (mkbdy args bdy) (Just bodyty) 

          mkbdy :: [(Bool, TIntermediate m Normal)] -> TIntermediate m Normal -> TIntermediate m Normal
          mkbdy [] bdy = bdy
          mkbdy ((implicit, term):xs) bdy =
            if implicit then
              TImplApply (mkbdy xs bdy) term
            else
              TApply (mkbdy xs bdy) term

          -- justification for empty environment: the "inner" (bodyty) should be
          -- an application of the term to all unbound type variables, *and* 
          --fnlty :: Normal m
          fnlty =
            case unbound of 
              [] -> bodyty -- TODO: eval bodyty if empty
              ((ty, var) : xs) -> NormProd var Hidden ty (mkFnlBdy xs bodyty)

          mkFnlBdy :: [(Normal m, String)] -> Normal m -> Normal m
          mkFnlBdy [] ret = ret
          mkFnlBdy ((ty, var) : xs) ret = NormProd var Hidden ty (mkFnlBdy xs ret) 
          

  (TLambda args body mty) -> do 
     mty' <- case mty of
       Just (TIntermediate' val) -> Just <$> evalTIntermediate val env
       Nothing -> pure Nothing
     (args', mret) <- case mty' of
       Just ty -> annArgs ty args >>= (\(x, y) -> pure (x, Just y))
       Nothing -> pure (args, Nothing)
     (env', args'') <- updateFromArgs env args'
     (body', ty, subst) <- typeCheck body env'
     case mty' of 
       Nothing -> do
         let (fnlArgs, fnlsubst) = fixArgs args'' subst
         fnlTy <- buildFnType fnlArgs subst ty
         let fnl_lambda = TLambda fnlArgs body' (Just fnlTy)
         pure (fnl_lambda, fnlTy, fnlsubst)
       Just _ -> do
         let (fnlArgs, fnlsubst) = fixArgs args'' subst
         fnlTy <- buildFnType fnlArgs subst ty
         let fnl_lambda = TLambda fnlArgs body' (Just fnlTy)
         pure (fnl_lambda, fnlTy, fnlsubst)

     where 
       buildFnType :: MonadError String m => [(TArg m Normal, ArgType)] -> Subst m -> Normal m -> m (Normal m) 
       buildFnType [] _ bodyty = pure bodyty
       -- TODO: consider substitutions!
       buildFnType ((ty, aty):tys) subst bodyty = do
         ret_ty <- buildFnType tys subst bodyty
         case ty of 
           BoundArg str t ->
             case aty of  
               Hidden ->
                 if Set.member str (free ret_ty) then
                   pure (NormProd str Visible t ret_ty)
                 else
                   pure (NormArr t ret_ty)
               Visible ->
                 if Set.member str (free ret_ty) then
                   pure (NormProd str Hidden t ret_ty)
                 else
                   throwError "bound types must be deducible in implicit products"
               
           InfArg _ _ -> 
             throwError "buildFnType not expecting inference!"

       -- fixArgs will take a list of Typed arguments, and convert any
       -- inference arguments to string arguments
       fixArgs :: [(TArg m Normal, ArgType)] -> Subst m -> ([(TArg m Normal, ArgType)], Subst m)
       fixArgs args subst =
         let (args', subst', impl) = fixArgs' args subst
         in (map (\str -> (BoundArg str (NormUniv 0), Hidden)) impl <> args', subst')
         

       fixArgs' :: [(TArg m Normal, ArgType)] -> Subst m -> ([(TArg m Normal, ArgType)], Subst m, [String])
       fixArgs' [] subst = ([], subst, [])
       fixArgs' ((arg, isImpl) : args) subst =
         let (args', subst', impl) = fixArgs' args subst in
           case arg of
             BoundArg str ty -> (((BoundArg str ty, isImpl) : args'), subst', impl)
             -- TOOD: come up with a better solution to new names...
             InfArg nme id -> case findStrSubst ("#" <> show id) subst of
               Just ty -> (((BoundArg nme ty, isImpl) : args'),
                           rmSubst ("#" <> show id) subst',
                           impl)
               Nothing -> ((BoundArg nme (mkVar ("#" <> show id)), isImpl) : args',
                           subst',
                           ("#" <> show id) : impl)

       -- ann args takes a type annotation and argument list, and will annotate
       -- the arguments based on the type
       -- TODO consider the inference status of an argument!
       annArgs :: MonadError String m => Normal m -> [(TArg m TIntermediate', ArgType)] -> m ([(TArg m TIntermediate', ArgType)], Normal m)
       annArgs ret [] = pure ([], ret)
       annArgs ty ((arg, bl) : args) = case arg of 
         InfArg str id -> do
           head <- tyHead ty
           tail <- tyTail ty
           (args', ret) <- annArgs tail args 
           pure ((BoundArg str (TIntermediate' (TValue head)), bl) : args, ret)
           -- TOOD
           -- BoundArg str ty
           -- TWildCard ty

  (TProd (arg, bl) body) -> do
    case arg of  
      BoundArg var (TIntermediate' ty) -> do
        ty' <- evalTIntermediate ty env
        (body', bodyTy, subst) <- typeCheck body (Env.insert var (Neu (NeuVar var ty') ty') ty' env)
        pure (TProd (BoundArg var ty', bl) body', NormUniv 0, subst)
      TWildCard (TIntermediate' ty) -> do
        ty' <- evalTIntermediate ty env
        (body', bodyTy, subst) <- typeCheck body env
        pure (TProd (TWildCard ty', bl) body', NormUniv 0, subst)

  (TAccess term field) -> do
    (term', ty, subst) <- typeCheck term env

    -- TODO: signatures need types?
    -- TODO: what if there is a substituion 
    case ty of 
      (NormSig map) -> case getField field map of 
        Just ty -> pure (TAccess term' field, ty, subst)
        Nothing -> throwError ("cannot find field " <> field)
      t -> throwError ("expected signature, got " <> show t)
         
       
  (TIF cond e1 e2 Nothing) -> do 
    (cond', tcond, substcond) <- typeCheck cond env
    (e1', te1, subste1) <- typeCheck e1 env
    (e2', te2, subste2) <- typeCheck e2 env
    (capp, _, substcnd') <- constrain tcond (PrimType BoolT) env
    (lapp, rapp, substterms) <- constrain te1 te2 env

    let cond'' = mkApp cond' capp
        e1'' = mkApp e1' lapp
        e2'' = mkApp e2' rapp
    
    s1 <- compose substcond subste1 
    s2 <- compose s1 subste2 
    s3 <- compose s2 substcnd'
    s4 <- compose s3 substterms
    fnlTy <- doSubst s4 te1
    pure (TIF cond'' e1'' e2'' (Just fnlTy), fnlTy, s4)

  (TStructure defs Nothing) -> do  
    let foldDefs :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [TDefinition m TIntermediate'] -> Environment m
                 -> m ([TDefinition m Normal], [(String, Normal m)], Subst m)
        foldDefs [] _ = pure ([], [], nosubst)
        foldDefs (def : defs) env = do
          (def', deflist, subst) <- typeCheckDef def env
          (defs', fields, subst') <- foldDefs defs (foldr (\(var, val) env ->
                                                             Env.insert var (Neu (NeuVar var val) val) val env)
                                                     env deflist)
          fnlSubst <- compose subst subst'
          pure (def' : defs',  deflist <> fields, fnlSubst)
          
    (defs', fields, subst) <- foldDefs defs env

    pure (TStructure defs' (Just (NormSig fields)), NormSig fields, subst)

  (TSignature defs) -> do  
    let foldDefs :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [TDefinition m TIntermediate'] -> Environment m
                 -> m ([TDefinition m Normal], [(String, Normal m)], Subst m)
        foldDefs [] _ = pure ([], [], nosubst)
        foldDefs (def : defs) env = do
          (def', deflist, subst) <- typeCheckDef def env
          (defs', fields, subst') <- foldDefs defs (foldr (\(var, val) env ->
                                                             Env.insert var (Neu (NeuVar var val) val) val env)
                                                     env deflist)
          fnlSubst <- compose subst subst'
          pure (def' : defs',  deflist <> fields, fnlSubst)
          
    (defs', fields, subst) <- foldDefs defs env

    pure (TSignature defs', NormUniv 0, subst)

  (TMatch term patterns Nothing) -> do
    (term', ty, subst) <- typeCheck term env
    retTy <- freshVar 
    (patterns', subst') <- checkPatterns patterns ty retTy
    outSubst <- compose subst subst'
    -- TODO: check if there is a ready substitution

    retTy' <- doSubst outSubst retTy

    let fnlSubst = rmSubst (show retTy) outSubst
    pure $ (TMatch term' patterns' (Just retTy'), retTy', fnlSubst)
    where
      -- Check Patterns: take a list of patterns as input, along with the
      -- matching type and return type, to be unified with
      -- return a pattern, the return type of that pattern and the required substituion
      -- checkPatterns :: [(TPattern m TIntermediate', TIntermediate m TIntermediate')] -> Normal m -> Normal m
      --               -> m ([(TPattern m Normal, TIntermediate m Normal)], Subst m)
      checkPatterns [] _ _ = pure ([], nosubst)
      checkPatterns ((p, e) : ps) matchty retty = do
        -- an updated pattern, and the type thereof  
        (p', matchty', envUpd) <- getPatternType p
        
        let env' = foldr (\(sym, ty) env -> Env.insert sym (Neu (NeuVar sym ty) ty) ty env) env envUpd
        (e', eret, esubst) <- typeCheck e env'

        -- TODO: ensure that the constrains are right way round...
        -- TODO: what to do with lapp1, lapp2 etc...
        (lapp1, rapp1, restMatchSubst) <- constrain matchty matchty' env
        (lapp2, rapp2, restRetSubst) <- constrain retty eret env
        (ps', pssubst) <- checkPatterns ps matchty retty
        restRetSubst' <- varRight restRetSubst

        if not (null lapp1 && null lapp2 && null rapp1 && null rapp2) then 
          throwError "constrain application in CheckPatterns not null"
          else pure ()
  
        -- TODO: make sure composition is right way round...
        substFnl <- composeList restRetSubst' [pssubst, restMatchSubst, esubst]
        pure $ ((p', e') : ps', substFnl)
      
      -- TODO: check for duplicate variables!
      -- Return a tuple of:
      -- 1. The updated pattern,
      -- 2. The value of the type to be matched against
      -- 3. A list of bindings of strings to types 
        
      --getPatternType :: TPattern m TIntermediate' -> m (TPattern m Normal, Normal m, [(String, Normal m)])
      getPatternType TWildPat = do
        ty <- freshVar
        pure (TWildPat, ty, [])
      getPatternType (TBindPat sym Nothing) = do
        ty <- freshVar
        pure $ (TBindPat sym (Just ty), ty, [(sym, ty)])
      getPatternType (TIMatch indid altid strip (TIntermediate' ctorTy) subPatterns) = do 
        ctorTy' <- evalTIntermediate ctorTy env
        let types = getTypes (dropTypes strip ctorTy')
        lst <- mapM getPatternType' (zip subPatterns types)
        let (subPatterns', types, binds) = foldr (\(p, t, b) (ps, ts, bs) -> (p:ps, t:ts, b<>bs))
                                                 ([], [], []) lst
        pure $ (TIMatch indid altid strip ctorTy' subPatterns',
                fnlType ctorTy',
                binds)
        -- TODO: use returned types for some kind of constraint??
      getPatternType (TBuiltinMatch fnc strip (TIntermediate' ty) pats) = do
        lst <- mapM getPatternType pats
        let (subpatterns', norms, vars) =
              foldr (\(s, n, v) (ss, ns, vs) -> (s:ss, n:ns, v <> vs)) ([], [], []) lst
        ty' <- evalTIntermediate ty env
        retty <- foldTyApp strip ty' norms
        pure $ (TBuiltinMatch fnc strip ty' subpatterns', retty, vars)
        where 
          foldTyApp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Int -> Normal m -> [Normal m] -> m (Normal m)
          foldTyApp 0 ty [] = pure ty
          foldTyApp 0 ty (n : ns) = do
            ty' <- Eval.tyApp ty n
            foldTyApp 0 ty' ns
          foldTyApp n (NormProd sym Hidden a b) apps = do
            b' <- foldTyApp (n - 1) b apps 
            pure $ NormProd sym Hidden a b'

      -- The secondary version takes in a list of types to constrain against
      getPatternType' :: Applicative m => (TPattern m TIntermediate', Normal m) -> m (TPattern m Normal, Normal m, [(String, Normal m)]) 
      getPatternType' (TWildPat, ty) =
        pure (TWildPat, ty, [])
      getPatternType' (TBindPat sym Nothing, ty) = 
        pure (TBindPat sym (Just ty), ty, [(sym, ty)])

  (TCoMatch patterns Nothing) -> do
    retTy <- freshVar 
    (patterns', subst) <- checkPatterns patterns retTy
  -- TODO: check if there is a ready substitution
    retTy' <- doSubst subst retTy
    let fnlSubst = rmSubst (show retTy) subst
    pure $ (TCoMatch patterns' (Just retTy'), retTy', fnlSubst)
    where
      -- Check Patterns: take a list of patterns as input, along with the
      -- matching type and return type, to be unified with
      -- return a pattern, the return type of that pattern and the required substituion
      -- checkPatterns :: [(TCoPattern m TIntermediate', TIntermediate m TIntermediate')] -> Normal m
      --               -> m ([(TCoPattern m Normal, TIntermediate m Normal)], Subst m)
      checkPatterns [] _ = pure ([], nosubst)
      checkPatterns ((p, e) : ps) retTy = do
        -- an updated pattern, and the type thereof  
        (p', fncRet, retTy', envUpd) <- getPatternType p
        
        let env' = foldr (\(sym, ty) env -> Env.insert sym (Neu (NeuVar sym ty) ty) ty env) env envUpd
        (e', bodyTy, esubst) <- typeCheck e env'

        -- TODO: ensure that the constrains are right way round...
        -- TODO: what to do with lapp1, lapp2 etc...
        (lapp1, rapp1, bodySubst) <- constrain fncRet bodyTy env
        (lapp2, rapp2, retSubst) <- constrain retTy retTy' env
        (ps', pssubst) <- checkPatterns ps retTy

        if not (null lapp1 && null lapp2 && null rapp1 && null rapp2) then
          throwError "non-null l/rapp in copattern check"
          else pure ()
  
        -- TODO: make sure composition is right way round...
        substFnl <- composeList retSubst [bodySubst, pssubst]
        pure $ ((p', e') : ps', substFnl)
      
      -- TODO: check for duplicate variable patterns!
      -- Get the type of a single pattern, to be constrained against.
      -- Also, return a list of variables and their types
        
      --getPatternType :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => TCoPattern m TIntermediate' -> m (TCoPattern m Normal, Normal m, Normal m, [(String, Normal m)])
      getPatternType (TCoinductPat name indid altid strip (TIntermediate' altTy) subpatterns) = do 
        altTy' <- evalTIntermediate altTy env
        let types = getTypes (dropTypes strip altTy')
            fncRetTy = fnlType altTy'
            retTy = head types
            args = tail types
            lst = map getPatternType' (zip args subpatterns)
            (subpatterns', norms, vars) = foldr (\(s, n, v) (ss, ns, vs) -> (s:ss, n:ns, v <> vs)) ([], [], []) lst 
        pure $ (TCoinductPat name indid altid strip altTy' subpatterns', fncRetTy, retTy, vars)

      getPatternType _ = throwError "comatch requires coterm as top-level pattern"
        
      getPatternType' :: (Normal m, TCoPattern m TIntermediate') -> (TCoPattern m Normal, Normal m, [(String, Normal m)])
      getPatternType' (ty, TCoWildPat) = (TCoWildPat, ty, [])
      getPatternType' (ty, TCoBindPat sym Nothing) = (TCoBindPat sym (Just ty), ty, [(sym, ty)])


  
  (TAdaptForeign lang lib types Nothing) -> do
    types' <- mapM (\(s1, s2, (TIntermediate' i)) -> (,,) s1 s2 <$> evalTIntermediate i env) types
    let ty = NormSig $ map (\(s, _, v) -> (s, v)) types'
    pure $ (TAdaptForeign lang lib types' (Just ty), ty, nosubst)
     
    
      
  other -> 
    throwError ("typecheck unimplemented for intermediate term " <> show other)

  where
    updateFromArgs :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Environment m -> [(TArg m TIntermediate', ArgType)] -> m (Environment m, [(TArg m Normal, ArgType)])
    updateFromArgs ctx [] = pure (ctx, [])
    updateFromArgs ctx ((arg, bl) : args) = do 
      case arg of
        BoundArg str (TIntermediate' ty) -> do
          ty' <- evalTIntermediate ty ctx
          (ctx', args') <- updateFromArgs (Env.insert str (Neu (NeuVar str ty') ty') ty' ctx) args
          pure (Env.insert str (Neu (NeuVar str ty') ty') ty' ctx', ((BoundArg str ty', bl) : args'))
        InfArg str id -> do
          (ctx', args') <- updateFromArgs ctx args
          pure (Env.insert str (Neu (NeuVar str (mkVar ("#" <> show id))) (mkVar ("#" <> show id))) (mkVar ("#" <> show id))  ctx',
                               (InfArg str id, bl) : args')


  

typeCheckDef :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => TDefinition m TIntermediate' -> Environment m
             -> m (TDefinition m Normal, [(String, Normal m)], Subst m)
typeCheckDef (TSingleDef name body ty) ctx = do
  bnd <- case ty of 
    Nothing -> freshVar
    Just (TIntermediate' ty) -> evalTIntermediate ty ctx
  (body', ty', subst) <- typeCheck body (Env.insert name (Neu (NeuVar name bnd) bnd) bnd ctx)
  pure (TSingleDef name body' (Just ty'), [(name, ty')], subst)

typeCheckDef (TInductDef sym id params (TIntermediate' ty) alts) ctx = do
  -- TODO: check alternative definitions are well-formed (positive, return
  -- correct Constructor) 
  ty' <- evalTIntermediate ty ctx
  index <- readIndex ty'
  (ctx', params') <- updateFromParams params ctx
  let (indCtor, indTy) = mkIndexTy params' index ty' id
  alts' <- processAlts alts params' (Env.insert sym indCtor indTy ctx')

  let defs = ((sym, indCtor) : mkAltDefs alts')
      mkAltDefs :: [(String, Int, Normal m)] -> [(String, Normal m)]
      mkAltDefs [] = []
      mkAltDefs ((sym, altid, ty) : alts) =
          let alt = NormIVal sym id altid (length params) [] ty
              alts' = mkAltDefs alts
          in ((sym, alt) : alts')
  pure $ (TInductDef sym id params' indCtor alts', defs, nosubst)
  where
    processAlts :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Int, TIntermediate' m)] -> [(String, Normal m)] -> Environment m
                -> m [(String, Int, Normal m)]
    processAlts [] params ctx = pure []
    processAlts ((sym, id, (TIntermediate' ty)) : alts) ps ctx = do
      -- TODO: check for well-formedness!!
      -- TODO: positivity check
      ty' <- evalTIntermediate ty ctx
      alts' <- processAlts alts ps ctx
      pure $ (sym, id, (captureParams ps ty')) : alts'
      where
        captureParams [] ty = ty
        captureParams ((sym, ty) : ps) tl = NormProd sym Hidden ty (captureParams ps tl)

    updateFromParams :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, TIntermediate' m)] -> Environment m -> m (Environment m, [(String, Normal m)])
    updateFromParams [] ctx = pure (ctx, [])
    updateFromParams ((sym, TIntermediate' ty) : args) ctx = do
      ty' <- evalTIntermediate ty ctx
      (ctx', args') <- updateFromParams args (Env.insert sym (Neu (NeuVar sym ty') ty') ty' ctx)
      pure (Env.insert sym (Neu (NeuVar sym ty') ty') ty' ctx', ((sym, ty') : args'))

    readIndex :: (MonadState (ProgState m) m, MonadError String m) => Normal m -> m [(String, Normal m)]
    readIndex (NormUniv n) = pure []
    readIndex (NormProd sym Visible a b) = do 
      tl  <- readIndex b
      pure ((sym, a) : tl)
    readIndex (NormArr a b) = do
      id <- freshVar
      tl  <- readIndex b
      pure ((show id, a) : tl)
    readIndex _ = throwError "bad inductive type annotation"

    -- take first the parameters, then and the index, along with the index's type.  
    -- return a constructor for the type, and the type of the constructor
    mkIndexTy :: [(String, Normal m)] -> [(String, Normal m)] -> Normal m -> Int -> (Normal m, Normal m)
    mkIndexTy params index ty id = mkIndexTy' params index (ty, id) []
    mkIndexTy' :: [(String, Normal m)] -> [(String, Normal m)] -> (Normal m, Int) -> [(String, Normal m)] -> (Normal m, Normal m) 
    mkIndexTy' [] [] (ty, id) args = 
      (NormIType sym id (reverse (map (\(sym, ty) -> (Neu (NeuVar sym ty) ty)) args)), ty)

    mkIndexTy' ((sym, ty) : params) index body args = do
      let (ctor, ctorty) = mkIndexTy' params index body ((sym, ty) : args)
          fty = NormProd sym Visible ty ctorty
        in (NormAbs sym ctor fty, fty)

    mkIndexTy' [] ((sym, ty) : ids) index args = do
      let (ctor, ctorty) = mkIndexTy' [] ids index ((sym, ty) : args)
        in (NormAbs sym ctor ctorty, ctorty)


typeCheckDef def _ = do
  throwError ("typeCheckDef not implemented for")


annotate :: MonadError String m => TIntTop m TIntermediate' -> Normal m -> m (TIntTop m TIntermediate')
annotate (TDefinition (TSingleDef str val _)) ty =
  pure . TDefinition $ TSingleDef str val (Just $ TIntermediate' $ TValue ty)
annotate _ _ = throwError "annotation must be followed by definition"




-- PRIVATE FUNCTIONS  
      
-- Apply a term to a list of normal values
mkApp :: TIntermediate m Normal -> [Normal m] -> TIntermediate m Normal
mkApp term [] = term
mkApp term (v:vs) = mkApp (TApply term (TValue v)) vs

tyApp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m -> [Normal m] -> m (Normal m)
tyApp ty [] = pure ty
tyApp (NormArr l r) (v:vs) = tyApp r vs
tyApp (NormProd s Visible a b) (v:vs) = Eval.normSubst (v, s) b >>= (\n -> tyApp n vs)
tyApp (NormProd s Hidden a b) (v:vs) = Eval.normSubst (v, s) b >>= (\n -> tyApp n vs)


evalTIntermediate :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => TIntermediate m TIntermediate' -> Environment m -> m (Normal m)  
evalTIntermediate tint ctx = do 
  (checked, _, _) <- typeCheck tint ctx -- TODO: dodge??
  c_term <- Conv.toCore checked
  local (const ctx) (Eval.eval c_term) 

evalNIntermediate :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => TIntermediate m Normal -> Environment m -> m (Normal m)  
evalNIntermediate tint env = do 
  c_term <- Conv.toCore tint
  local (const env) (Eval.eval c_term) 

getTypes (NormArr l r) = l : getTypes r
getTypes (NormProd _ _ a b) = a : getTypes b
getTypes _ = []

dropTypes 0 t = t
dropTypes n (NormArr l r) = dropTypes (n-1) r
dropTypes n (NormProd _ _ _ b) = dropTypes (n-1) b

fnlType (NormArr l r) = fnlType r 
fnlType (NormProd _ _ _ b) = fnlType b
fnlType t = t
