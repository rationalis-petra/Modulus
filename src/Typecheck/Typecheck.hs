module Typecheck.Typecheck where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except (runExcept)
import Control.Monad.State 
-- import Control.Lens 

  
import Debug.Trace
import Data (PrimType(..),
             Normal,
             Normal'(..),
             Core(..),
             Neutral,
             Neutral'(..),
             var_counter,
             EvalM)
import Syntax.TIntermediate

import qualified Interpret.Environment as Env
import qualified Syntax.Conversions as Conv 
import Interpret.EvalM
import qualified Interpret.Eval as Eval
import Syntax.Utils (typeVal, free, getField, mkVar)

import qualified Typecheck.Context as Ctx
import Typecheck.Constrain


err = throwError

typeCheckTop :: TIntTop TIntermediate' -> Ctx.Context
             -> EvalM (Either (TIntTop Normal, Normal) (TIntTop Normal))
typeCheckTop (TExpr e) ctx = do
      (expr, ty, subst) <- typeCheck e ctx
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
          (Ctx.insert name (Neu (NeuVar name recTy) recTy) recTy ctx)
      (_, app, csubst) <- constrain recTy ty ctx
      let (fnlSubstl, fnlSubstr) = rmSubst (show recTy) csubst
      ty' <- tyApp ty app
      if (null fnlSubstl && null fnlSubstr)
        then 
          pure $ Right $ TDefinition $ TSingleDef name expr' (Just ty')
        else do
          throwError ("subst strings non empty at toplevel: " <> show (fnlSubstl, fnlSubstr))

    TSingleDef name expr (Just mty) -> do
      throwError "cannot check type-annotated single definitions"

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
      alts' <- processAlts alts params' (Ctx.insert sym indCtor indTy ctx')
      pure $ Right $ TDefinition $ TInductDef sym id params' indCtor alts'

      where
        processAlts :: [(String, Int, TIntermediate')] -> [(String, Normal)] -> Ctx.Context
                    -> EvalM [(String, Int, Normal)]
        processAlts [] params ctx = pure []
        processAlts ((sym, id, (TIntermediate' ty)) : alts) ps ctx = do
          -- TODO: check for well-formedness!!
          -- TODO: positivity check
          ty' <- evalTIntermediate ty ctx
          alts' <- processAlts alts ps ctx
          pure $ (sym, id, (captureParams ps ty')) : alts'
          where
            captureParams [] ty = ty
            captureParams ((sym, ty) : ps) tl = NormImplProd sym ty (captureParams ps tl)

        updateFromParams :: [(String, TIntermediate')] -> Ctx.Context -> EvalM (Ctx.Context, [(String, Normal)])
        updateFromParams [] ctx = pure (ctx, [])
        updateFromParams ((sym, TIntermediate' ty) : args) ctx = do
          ty' <- evalTIntermediate ty ctx
          (ctx', args') <- updateFromParams args
                             (Ctx.insert sym (Neu (NeuVar sym ty') ty') ty' ctx)
          pure (Ctx.insert sym (Neu (NeuVar sym ty') ty') ty' ctx', ((sym, ty') : args'))

        readIndex :: Normal -> EvalM [(String, Normal)]
        readIndex (NormUniv n) = pure []
        readIndex (NormProd sym a b) = do 
          tl  <- readIndex b
          pure ((sym, a) : tl)
        readIndex (NormArr a b) = do
          id <- freshVar
          tl  <- readIndex b
          pure ((show id, a) : tl)
        readIndex _ = throwError "bad inductive type annotation"

        -- take first the parameters, then and the index, along with the index's type.  
        -- return a constructor for the type, and the type of the constructor
        mkIndexTy :: [(String, Normal)] -> [(String, Normal)] -> Normal -> Int -> EvalM (Normal, Normal)
        mkIndexTy params index ty id = mkIndexTy' params index (ty, id) []
        mkIndexTy' :: [(String, Normal)] -> [(String, Normal)] -> (Normal, Int) -> [(String, Normal)] -> EvalM (Normal, Normal) 
        mkIndexTy' [] [] (ty, id) args = do 
          pure (NormIType sym id (reverse (map (\(var, ty) -> Neu (NeuVar var ty) ty) args)), ty)

        mkIndexTy' ((sym, ty) : params) index body args = do
          (ctor, ctorty) <- mkIndexTy' params index body ((sym, ty) : args)
          let fty = NormProd sym ty ctorty
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
      alts' <- processAlts alts params' (Ctx.insert sym indCtor indTy ctx')
      pure $ Right $ TDefinition $ TCoinductDef sym id params' indCtor alts'

      where
        processAlts :: [(String, Int, TIntermediate')] -> [(String, Normal)] -> Ctx.Context
                    -> EvalM [(String, Int, Normal)]
        processAlts [] params ctx = pure []
        processAlts ((sym, id, (TIntermediate' ty)) : alts) ps ctx = do
          -- TODO: check for well-formedness!!
          -- TODO: positivity check
          ty' <- evalTIntermediate ty ctx
          alts' <- processAlts alts ps ctx
          pure $ (sym, id, (captureParams ps ty')) : alts'
          where
            captureParams [] ty = ty
            captureParams ((sym, ty) : ps) tl = NormImplProd sym ty (captureParams ps tl)

        updateFromParams :: [(String, TIntermediate')] -> Ctx.Context -> EvalM (Ctx.Context, [(String, Normal)])
        updateFromParams [] ctx = pure (ctx, [])
        updateFromParams ((sym, TIntermediate' ty) : args) ctx = do
          ty' <- evalTIntermediate ty ctx
          (ctx', args') <- updateFromParams args
                             (Ctx.insert sym (Neu (NeuVar sym ty') ty') ty' ctx)
          pure (Ctx.insert sym (Neu (NeuVar sym ty') ty') ty' ctx', ((sym, ty') : args'))

        readIndex :: Normal -> EvalM [(String, Normal)]
        readIndex (NormUniv n) = pure []
        readIndex (NormProd sym a b) = do 
          tl  <- readIndex b
          pure ((sym, a) : tl)
        readIndex (NormArr a b) = do
          id <- freshVar
          tl  <- readIndex b
          pure ((show id, a) : tl)
        readIndex _ = throwError "bad inductive type annotation"

        -- take first the parameters, then and the index, along with the index's type.  
        -- return a constructor for the type, and the type of the constructor
        mkIndexTy :: [(String, Normal)] -> [(String, Normal)] -> Normal -> Int -> EvalM (Normal, Normal)
        mkIndexTy params index ty id = mkIndexTy' params index (ty, id) []
        mkIndexTy' :: [(String, Normal)] -> [(String, Normal)] -> (Normal, Int) -> [(String, Normal)] -> EvalM (Normal, Normal) 
        mkIndexTy' [] [] (ty, id) args = do 
          pure (NormIType sym id (reverse (map (\(var, ty) -> Neu (NeuVar var ty) ty) args)), ty)

        mkIndexTy' ((sym, ty) : params) index body args = do
          (ctor, ctorty) <- mkIndexTy' params index body ((sym, ty) : args)
          let fty = NormProd sym ty ctorty
          pure $ (NormAbs sym ctor fty, fty)

        mkIndexTy' [] ((sym, ty) : ids) index args = do
          (ctor, ctorty) <- mkIndexTy' [] ids index ((sym, ty) : args)
          pure $ (NormAbs sym ctor ctorty, ctorty)
          


typeCheck :: TIntermediate TIntermediate' -> Ctx.Context -> EvalM (TIntermediate Normal, Normal, Subst)
typeCheck expr ctx = case expr of
  (TValue v) -> do
    t <- liftExcept (typeVal v)
    pure (TValue v, t, nosubst)

  (TSymbol s) -> do
    case runExcept (Ctx.lookup s ctx) of 
      Right (_, ty) -> pure (TSymbol s, ty, nosubst)
      Left err -> throwError ("couldn't find type of symbol " <> s <> " err-msg: " <> err)

  
  (TImplApply l r) -> do 
    (l', tl, substl) <- typeCheck l ctx
    (r', tr, substr) <- typeCheck r ctx
    substboth <- compose substl substr
    case tl of  
      NormImplProd var t1 t2 -> do
        (lapp, rapp, substcomb) <- constrain t1 tr ctx
        subst <- compose substcomb substboth
        appTy <- evalNIntermediate r' ctx
        retTy <- Eval.normSubst (appTy, var) t2
        pure (TImplApply l' r', retTy, subst)
      t -> throwError ("implicit application to non-implicit type" <> show t)

  (TApply l r) -> do 
    (l', tl, substl) <- typeCheck l ctx
    (r', tr, substr) <- typeCheck r ctx
    substboth <- compose substl substr
    case tl of  
      NormArr t1 t2 -> do 
        (_, app, substcomb) <- constrain t1 tr ctx
        let r'' = mkApp r' app
        subst <- compose substcomb substboth
        pure (TApply l' r'', t2, subst)
      NormProd var a t2 -> do 
        (_, app, substcomb) <- constrain a tr ctx
        subst <- compose substcomb substboth
        depApp <- evalNIntermediate r' ctx
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
      deriveFn :: Normal -> Normal -> TIntermediate Normal
               -> EvalM ([(Bool, TIntermediate Normal)], [(Normal, String)], Subst, Normal)
      deriveFn (NormImplProd var a t2) tr r = do
        (args, unbnd, subst, rettype) <- deriveFn t2 tr r
        case findStrSubst var subst of 
          Just val -> do
            val' <- inferVar val a ctx
            retTy <- Eval.normSubst (val', var) rettype
            pure (((True, (TValue val')) : args),
                           unbnd,
                           rmSubst var subst,
                           retTy)
          Nothing -> pure ((True, TValue (mkVar var)) : args, ((NormUniv 0, var):unbnd),
                           rmSubst var subst, rettype)
      deriveFn (NormArr t1 t2) tr r = do
        (app, lapp, subst) <- constrain tr t1 ctx
        pure ([(False, mkApp r app)], [], subst, t2)
      deriveFn t tr r = do
        var' <- freshVar 
        (lapp, rapp, subst) <- constrain (NormArr tr var') t ctx
        -- TODO
        -- if not (null lapp && null rapp) then err "unsure of how to handle non-empty l/rapp in deriveFn"
        -- else
        pure ([(False, r)], [], subst, var')

      mkFnlFn :: [(Bool, TIntermediate Normal)] -> [(Normal, String)] -> TIntermediate Normal -> Normal
              -> (TIntermediate Normal, Normal)
      mkFnlFn args unbound bdy bodyty = (fnlfn, fnlty)
        where
          fnlfn :: TIntermediate Normal
          fnlfn = if (null args)
            then
              (mkbdy [] bdy)
            else
              TLambda (map (\(ty, s) -> (BoundArg s ty, True)) unbound) (mkbdy args bdy) (Just bodyty) 
          mkbdy [] bdy = bdy
          mkbdy ((implicit, term):xs) bdy =
            if implicit then
              TImplApply (mkbdy xs bdy) term
            else
              TApply (mkbdy xs bdy) term

          -- justification for empty environment: the "inner" (bodyty) should be
          -- an application of the term to all unbound type variables, *and* 
          fnlty :: Normal
          fnlty =
            case unbound of 
              [] -> bodyty -- TODO: eval bodyty if empty
              ((ty, var) : xs) -> NormImplProd var ty (mkFnlBdy xs bodyty)
          mkFnlBdy :: [(Normal, String)] -> Normal -> Normal
          mkFnlBdy [] ret = ret
          mkFnlBdy ((ty, var) : xs) ret = NormImplProd var ty (mkFnlBdy xs ret) 
          

  (TLambda args body mty) -> do 
     (ctx', args') <- updateFromArgs ctx args
     (body', ty, subst) <- typeCheck body ctx'
     case mty of 
       Nothing -> do
         let (fnlArgs, fnlsubst) = fixArgs args' subst
         fnlTy <- buildFnType fnlArgs subst ty
         let fnl_lambda = TLambda fnlArgs body' (Just fnlTy)
         pure (fnl_lambda, fnlTy, fnlsubst)

     where 
       buildFnType :: [(TArg Normal, Bool)] -> Subst -> Normal -> EvalM Normal 
       buildFnType [] _ bodyty = pure bodyty
       -- TODO: consider substitutions!
       buildFnType ((ty, bl):tys) subst bodyty = do
         ret_ty <- buildFnType tys subst bodyty
         case ty of 
           BoundArg str t ->
             if bl then  
               if Set.member str (free ret_ty) then
                 pure (NormImplProd str t ret_ty)
               else
                 throwError "bound types must be deducible in implicit products"
             else
               if Set.member str (free ret_ty) then
                 pure (NormProd str t ret_ty)
               else
                 pure (NormArr t ret_ty)
               
           InfArg _ _ -> 
             throwError "buildFnType not expecting inference!"

       -- fixArgs will take a list of Typed arguments, and convert any
       -- inference arguments to string arguments
       fixArgs :: [(TArg Normal, Bool)] -> Subst -> ([(TArg Normal, Bool)], Subst)
       fixArgs args subst =
         let (args', subst', impl) = fixArgs' args subst
         in (map (\str -> (BoundArg str (NormUniv 0), True)) impl <> args', subst')
         

       fixArgs' :: [(TArg Normal, Bool)] -> Subst -> ([(TArg Normal, Bool)], Subst, [String])
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

  (TProd (arg, bl) body) -> do
    case arg of  
      BoundArg var (TIntermediate' ty) -> do
        ty' <- evalTIntermediate ty ctx
        (body', bodyTy, subst) <- typeCheck body (Ctx.insert var (Neu (NeuVar var ty') ty') ty' ctx)
        pure (TProd (BoundArg var ty', bl) body', NormUniv 0, subst)
      TWildCard (TIntermediate' ty) -> do
        ty' <- evalTIntermediate ty ctx
        (body', bodyTy, subst) <- typeCheck body ctx
        pure (TProd (TWildCard ty', bl) body', NormUniv 0, subst)

  (TAccess term field) -> do
    (term', ty, subst) <- typeCheck term ctx
    -- TODO: what if there is a substituion 
    case ty of 
      (NormSig map) -> case getField field map of 
        Just ty -> pure (TAccess term' field, ty, subst)
        Nothing -> throwError ("cannot find field " <> field)
      t -> throwError ("expected signature, got " <> show t)
         
       
  (TIF cond e1 e2 Nothing) -> do 
    (cond', tcond, substcond) <- typeCheck cond ctx
    (e1', te1, subste1) <- typeCheck e1 ctx
    (e2', te2, subste2) <- typeCheck e2 ctx
    (capp, _, substcnd') <- constrain tcond (PrimType BoolT) ctx
    (lapp, rapp, substterms) <- constrain te1 te2 ctx

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
    let foldDefs :: [TDefinition TIntermediate'] -> Ctx.Context
                 -> EvalM ([TDefinition Normal], [(String, Normal)], Subst)
        foldDefs [] _ = pure ([], [], nosubst)
        foldDefs (def : defs) ctx = do
          (def', deflist, subst) <- typeCheckDef def ctx
          (defs', fields, subst') <- foldDefs defs (foldr (\(var, val) ctx ->
                                                             Ctx.insert var (Neu (NeuVar var val) val) val ctx)
                                                     ctx deflist)
          fnlSubst <- compose subst subst'
          pure (def' : defs',  deflist <> fields, fnlSubst)
          
    (defs', fields, subst) <- foldDefs defs ctx

    pure (TStructure defs' (Just (NormSig fields)), NormSig fields, subst)

  (TSignature defs) -> do  
    let foldDefs :: [TDefinition TIntermediate'] -> Ctx.Context
                 -> EvalM ([TDefinition Normal], [(String, Normal)], Subst)
        foldDefs [] _ = pure ([], [], nosubst)
        foldDefs (def : defs) ctx = do
          (def', deflist, subst) <- typeCheckDef def ctx
          (defs', fields, subst') <- foldDefs defs (foldr (\(var, val) ctx ->
                                                             Ctx.insert var (Neu (NeuVar var val) val) val ctx)
                                                     ctx deflist)
          fnlSubst <- compose subst subst'
          pure (def' : defs',  deflist <> fields, fnlSubst)
          
    (defs', fields, subst) <- foldDefs defs ctx

    pure (TSignature defs', NormUniv 0, subst)

  (TMatch term patterns Nothing) -> do
    (term', ty, subst) <- typeCheck term ctx
    retTy <- freshVar 
    (patterns', subst') <- checkPatterns patterns ty retTy
    outSubst <- compose subst subst'
  -- TODO: check if there is a ready substitution
    retTy' <- doSubst outSubst retTy
    let fnlSubst' = rmSubst (show retTy) outSubst
        fnlSubst = trace ("final subst: " <> show fnlSubst') fnlSubst'
    pure $ (TMatch term' patterns' (Just retTy'), retTy', fnlSubst)
    where
      -- Check Patterns: take a list of patterns as input, along with the
      -- matching type and return type, to be unified with
      -- return a pattern, the return type of that pattern and the required substituion
      checkPatterns :: [(TPattern TIntermediate', TIntermediate TIntermediate')] -> Normal -> Normal
                    -> EvalM ([(TPattern Normal, TIntermediate Normal)], Subst)
      checkPatterns [] _ _ = pure ([], nosubst)
      checkPatterns ((p, e) : ps) matchty retty = do
        -- an updated pattern, and the type thereof  
        (p', matchty', ctxUpd) <- getPatternType p
        
  
        let ctx' = foldr (\(sym, ty) ctx -> Ctx.insert sym (Neu (NeuVar sym ty) ty) ty ctx) ctx ctxUpd
        (e', eret, esubst) <- typeCheck e ctx'

        -- TODO: ensure that the constrains are right way round...
        -- TODO: what to do with lapp1, lapp2 etc...
        (lapp1, rapp1, restMatchSubst) <- constrain matchty matchty' ctx
        (lapp2, rapp2, restRetSubst) <- constrain retty eret ctx
        (ps', pssubst) <- checkPatterns ps matchty retty
        restRetSubst' <- varRight restRetSubst

        let traceString = ("For: " <> show p) <> "\n"
                          <> ("matchty, matchty' " <> show matchty <> ", " <> show matchty') <> "\n"
                          <> ("retty, eret:  " <> show retty <> ", " <> show eret) <> "\n\n"
                          <> ("restRetsubst' : " <> show restRetSubst') <> "\n"
                          <> ("pssubst : " <> show pssubst) <> "\n"
                          <> ("restMatchSubst' : "  <> show restMatchSubst) <> "\n"
                          <> ("esubst : " <> show esubst) <> "\n"
                          <> ("ctxUpd : " <> show ctxUpd) <> "\n"

        lapprepl <- pure $ trace traceString lapp1

        if not (null lapprepl && null lapp2 && null rapp1 && null rapp2) then 
          throwError "constrain application in CheckPatterns not null"
          else pure ()
  
        -- TODO: make sure composition is right way round...
        substFnl <- composeList restRetSubst' [pssubst, restMatchSubst, esubst]
        substFnl' <- pure $ trace ("substFnl: " <> show substFnl) substFnl
        pure $ ((p', e') : ps', substFnl')
      
      -- TODO: check for duplicate variables!
      -- Return a tuple of:
      -- 1. The updated pattern,
      -- 2. The value of the type to be matched against
      -- 3. A list if bindings of strings to types 
        
      getPatternType :: TPattern TIntermediate' -> EvalM (TPattern Normal, Normal, [(String, Normal)]) 
      getPatternType TWildPat = do
        ty <- freshVar
        pure (TWildPat, ty, [])
      getPatternType (TBindPat sym Nothing) = do
        ty <- freshVar
        pure $ (TBindPat sym (Just ty), ty, [(sym, ty)])
      getPatternType (TIMatch indid altid strip (TIntermediate' ctorTy) subPatterns) = do 
        ctorTy' <- evalTIntermediate ctorTy ctx
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
        ty' <- evalTIntermediate ty ctx
        retty <- foldTyApp strip ty' norms
        pure $ (TBuiltinMatch fnc strip ty' subpatterns', retty, vars)
        where 
          foldTyApp :: Int -> Normal -> [Normal] -> EvalM Normal
          foldTyApp 0 ty [] = pure ty
          foldTyApp 0 ty (n : ns) = do
            ty' <- Eval.tyApp ty n
            foldTyApp 0 ty' ns
          foldTyApp n (NormImplProd sym a b) apps = do
            b' <- foldTyApp (n - 1) b apps 
            pure $ NormImplProd sym a b'

      -- The secondary version takes in a list of types to constrain against
      getPatternType' :: (TPattern TIntermediate', Normal) -> EvalM (TPattern Normal, Normal, [(String, Normal)]) 
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
      checkPatterns :: [(TCoPattern TIntermediate', TIntermediate TIntermediate')] -> Normal
                    -> EvalM ([(TCoPattern Normal, TIntermediate Normal)], Subst)
      checkPatterns [] _ = pure ([], nosubst)
      checkPatterns ((p, e) : ps) retTy = do
        -- an updated pattern, and the type thereof  
        (p', fncRet, retTy', ctxUpd) <- getPatternType p
        
  
        let ctx' = foldr (\(sym, ty) ctx -> Ctx.insert sym (Neu (NeuVar sym ty) ty) ty ctx) ctx ctxUpd
        (e', bodyTy, esubst) <- typeCheck e ctx'

        -- TODO: ensure that the constrains are right way round...
        -- TODO: what to do with lapp1, lapp2 etc...
        (lapp1, rapp1, bodySubst) <- constrain fncRet bodyTy ctx
        (lapp2, rapp2, retSubst) <- constrain retTy retTy' ctx
        (ps', pssubst) <- checkPatterns ps retTy

        let trace_string = ("For: " <> show p <> "\n"
                            <> "ctxUpd: " <> show ctxUpd <> "\n"
                            <> "bodySubst: " <> show bodySubst <> "\n"
                            <> "retSubst: " <> show retSubst <> "\n"
                            <> "pssubst: " <> show pssubst <> "\n\n")
            lapp1' = trace trace_string lapp1

        if not (null lapp1' && null lapp2 && null rapp1 && null rapp2) then
          throwError "non-null l/rapp in copattern check"
          else pure ()
  
        -- TODO: make sure composition is right way round...
        substFnl <- composeList retSubst [bodySubst, pssubst]
        pure $ ((p', e') : ps', substFnl)
      
      -- TODO: check for duplicate variable patterns!
      -- Get the type of a single pattern, to be constrained against.
      -- Also, return a list of variables and their types
        
      getPatternType :: TCoPattern TIntermediate' -> EvalM (TCoPattern Normal, Normal, Normal, [(String, Normal)]) 
      getPatternType (TCoinductPat name indid altid strip (TIntermediate' altTy) subpatterns) = do 
        altTy' <- evalTIntermediate altTy ctx
        let types = getTypes (dropTypes strip altTy')
            fncRetTy = fnlType altTy'
            retTy = head types
            args = tail types
        lst <- mapM getPatternType' (zip args subpatterns)
        let (subpatterns', norms, vars) = foldr (\(s, n, v) (ss, ns, vs) -> (s:ss, n:ns, v <> vs)) ([], [], []) lst 
        pure $ (TCoinductPat name indid altid strip altTy' subpatterns', fncRetTy, retTy, vars)

      getPatternType _ = throwError "comatch requires coterm as top-level pattern"
        
      getPatternType' :: (Normal, TCoPattern TIntermediate') -> EvalM (TCoPattern Normal, Normal, [(String, Normal)]) 
      getPatternType' (ty, TCoWildPat) = pure (TCoWildPat, ty, [])
      getPatternType' (ty, TCoBindPat sym Nothing) = pure (TCoBindPat sym (Just ty), ty, [(sym, ty)])
      
  other -> 
    throwError ("typecheck unimplemented for intermediate term " <> show other)

  where
    updateFromArgs :: Ctx.Context -> [(TArg TIntermediate', Bool)] -> EvalM (Ctx.Context, [(TArg Normal, Bool)])
    updateFromArgs ctx [] = pure (ctx, [])
    updateFromArgs ctx ((arg, bl) : args) = do 
      case arg of
        BoundArg str (TIntermediate' ty) -> do
          ty' <- evalTIntermediate ty ctx
          (ctx', args') <- updateFromArgs (Ctx.insert str (Neu (NeuVar str ty') ty') ty' ctx) args
          pure (Ctx.insert str (Neu (NeuVar str ty') ty') ty' ctx', ((BoundArg str ty', bl) : args'))
        InfArg str id -> do
          (ctx', args') <- updateFromArgs ctx args
          pure (Ctx.insert str (Neu (NeuVar str (mkVar ("#" <> show id))) (mkVar ("#" <> show id))) (mkVar ("#" <> show id))  ctx',
                               (InfArg str id, bl) : args')



  

typeCheckDef :: TDefinition TIntermediate' -> Ctx.Context
             -> EvalM (TDefinition Normal, [(String, Normal)], Subst)
typeCheckDef (TSingleDef name body ty) ctx = do 
  bnd <- case ty of 
    Nothing -> freshVar
    Just (TIntermediate' ty) -> evalTIntermediate ty ctx
  (body', ty', subst) <- typeCheck body (Ctx.insert name (Neu (NeuVar name bnd) bnd) bnd ctx)
  pure (TSingleDef name body' (Just ty'), [(name, ty')], subst)

typeCheckDef (TInductDef sym id params (TIntermediate' ty) alts) ctx = do
  -- TODO: check alternative definitions are well-formed (positive, return
  -- correct Constructor) 
  ty' <- evalTIntermediate ty ctx
  index <- readIndex ty'
  (ctx', params') <- updateFromParams params ctx
  (indCtor, indTy) <- mkIndexTy params' index ty' id
  alts' <- processAlts alts params' (Ctx.insert sym indCtor indTy ctx')

  let defs = ((sym, indCtor) : mkAltDefs alts')
      mkAltDefs :: [(String, Int, Normal)] -> [(String, Normal)]
      mkAltDefs [] = []
      mkAltDefs ((sym, altid, ty) : alts) =
          let alt = NormIVal sym id altid (length params) [] ty
              alts' = mkAltDefs alts
          in ((sym, alt) : alts')
  pure $ (TInductDef sym id params' indCtor alts', defs, nosubst)
  where
    processAlts :: [(String, Int, TIntermediate')] -> [(String, Normal)] -> Ctx.Context
                -> EvalM [(String, Int, Normal)]
    processAlts [] params ctx = pure []
    processAlts ((sym, id, (TIntermediate' ty)) : alts) ps ctx = do
      -- TODO: check for well-formedness!!
      -- TODO: positivity check
      ty' <- evalTIntermediate ty ctx
      alts' <- processAlts alts ps ctx
      pure $ (sym, id, (captureParams ps ty')) : alts'
      where
        captureParams [] ty = ty
        captureParams ((sym, ty) : ps) tl = NormImplProd sym ty (captureParams ps tl)

    updateFromParams :: [(String, TIntermediate')] -> Ctx.Context -> EvalM (Ctx.Context, [(String, Normal)])
    updateFromParams [] ctx = pure (ctx, [])
    updateFromParams ((sym, TIntermediate' ty) : args) ctx = do
      ty' <- evalTIntermediate ty ctx
      (ctx', args') <- updateFromParams args (Ctx.insert sym (Neu (NeuVar sym ty') ty') ty' ctx)
      pure (Ctx.insert sym (Neu (NeuVar sym ty') ty') ty' ctx', ((sym, ty') : args'))

    readIndex :: Normal -> EvalM [(String, Normal)]
    readIndex (NormUniv n) = pure []
    readIndex (NormProd sym a b) = do 
      tl  <- readIndex b
      pure ((sym, a) : tl)
    readIndex (NormArr a b) = do
      id <- freshVar
      tl  <- readIndex b
      pure ((show id, a) : tl)
    readIndex _ = throwError "bad inductive type annotation"

    -- take first the parameters, then and the index, along with the index's type.  
    -- return a constructor for the type, and the type of the constructor
    mkIndexTy :: [(String, Normal)] -> [(String, Normal)] -> Normal -> Int -> EvalM (Normal, Normal)
    mkIndexTy params index ty id = mkIndexTy' params index (ty, id) []
    mkIndexTy' :: [(String, Normal)] -> [(String, Normal)] -> (Normal, Int) -> [(String, Normal)] -> EvalM (Normal, Normal) 
    mkIndexTy' [] [] (ty, id) args = do 
      pure (NormIType sym id (reverse (map (\(sym, ty) -> (Neu (NeuVar sym ty) ty)) args)), ty)

    mkIndexTy' ((sym, ty) : params) index body args = do
      (ctor, ctorty) <- mkIndexTy' params index body ((sym, ty) : args)
      let fty = NormProd sym ty ctorty
      pure $ (NormAbs sym ctor fty, fty)

    mkIndexTy' [] ((sym, ty) : ids) index args = do
      (ctor, ctorty) <- mkIndexTy' [] ids index ((sym, ty) : args)
      pure $ (NormAbs sym ctor ctorty, ctorty)
  


typeCheckDef def _ = do
  throwError ("typeCheckDef not implemented for")







  





      
-- Apply a term to a list of normal values
mkApp :: TIntermediate Normal -> [Normal] -> TIntermediate Normal
mkApp term [] = term
mkApp term (v:vs) = mkApp (TApply term (TValue v)) vs

tyApp :: Normal -> [Normal] -> EvalM Normal
tyApp ty [] = pure ty
tyApp (NormArr l r) (v:vs) = tyApp r vs
tyApp (NormProd s a b) (v:vs) = Eval.normSubst (v, s) b >>= (\n -> tyApp n vs)
tyApp (NormImplProd s a b) (v:vs) = Eval.normSubst (v, s) b >>= (\n -> tyApp n vs)

  
freshVar :: EvalM Normal  
freshVar = do
  id <- use var_counter 
  var_counter += 1
  pure (Neu (NeuVar ("#" <> show id) (NormUniv 0)) (NormUniv 0))


evalTIntermediate :: TIntermediate TIntermediate' -> Ctx.Context -> EvalM Normal  
evalTIntermediate tint ctx = do 
  (checked, _, _) <- typeCheck tint ctx -- TODO: dodge??
  c_term <- case runExcept (Conv.toCore checked) of 
        Left err -> throwError err
        Right val -> pure val
  local (Ctx.ctxToEnv ctx) (Eval.eval c_term) 

evalNIntermediate :: TIntermediate Normal -> Ctx.Context -> EvalM Normal  
evalNIntermediate tint ctx = do 
  c_term <- case runExcept (Conv.toCore tint) of 
        Left err -> throwError err
        Right val -> pure val
  local (Ctx.ctxToEnv ctx) (Eval.eval c_term) 

getTypes (NormArr l r) = l : getTypes r
getTypes (NormProd _ a b) = a : getTypes b
getTypes (NormImplProd _ a b) = a : getTypes b
getTypes _ = []

dropTypes 0 t = t
dropTypes n (NormArr l r) = dropTypes (n-1) r
dropTypes n (NormProd _ _ b) = dropTypes (n-1) b
dropTypes n (NormImplProd _ _ b) = dropTypes (n-1) b

fnlType (NormArr l r) = fnlType r 
fnlType (NormProd _ _ b) = fnlType b
fnlType (NormImplProd _ _ b) = fnlType b
fnlType t = t
