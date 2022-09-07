module Typecheck.Typecheck where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except (runExcept)
import Control.Monad.State 
-- import Control.Lens 

import Data (PrimType(..),
             Normal,
             Normal'(..),
             Core(..),
             Neutral,
             Neutral'(..),
             var_counter,
             EvalM)
import Syntax.TIntermediate

import qualified Typecheck.Context as Ctx
import qualified Interpret.Environment as Env
import qualified Syntax.Conversions as Conv 
import Interpret.EvalM
import qualified Interpret.Eval as Eval
import Syntax.Utils (typeVal, free, getField)

 -- TODO: check - types are expressions, or values ?!?



type LRSubst = ([(Normal, String)], [(Normal, String)], [(Normal, String)])
type Subst = [(Normal, String)]

err = throwError  

typeCheckTop :: TIntTop TIntermediate' -> Ctx.Context
             -> EvalM (Either (TIntTop Normal, Normal) (TIntTop Normal))
typeCheckTop (TExpr e) ctx = do
      (expr, ty, subst) <- typeCheck e ctx
      -- (expr', ty') <- buildDepFn expr ty
      pure $ Left $ (TExpr expr, ty)

typeCheckTop (TDefinition def) ctx = 
  case def of 
    TSingleDef name expr Nothing -> do
      recTy <- freshVar
      (expr', ty, vsubst) <- typeCheck expr (Ctx.insert name (Neu $ NeuVar name) recTy ctx)
      (_, app, csubst) <- constrain recTy ty
      let fnlSubst = rmSubst (show recTy) csubst
      ty' <- tyApp ty app
      if (null fnlSubst)
        then 
          pure $ Right $ TDefinition $ TSingleDef name expr' (Just ty')
        else do
          throwError ("subst strings non empty at toplevel: " <> show fnlSubst)

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
          (ctx', args') <- updateFromParams args (Ctx.insert sym (Neu $ NeuVar sym) ty' ctx)
          pure (Ctx.insert sym (Neu $ NeuVar sym) ty' ctx', ((sym, ty') : args'))

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
        mkIndexTy' :: [(String, Normal)] -> [(String, Normal)] -> (Normal, Int) -> [String] -> EvalM (Normal, Normal) 
        mkIndexTy' [] [] (ty, id) args = do 
          pure (NormIType sym id (reverse (map (Neu . NeuVar) args)), ty)

        mkIndexTy' ((sym, ty) : params) index body args = do
          (ctor, ctorty) <- mkIndexTy' params index body (sym : args)
          let fty = NormProd sym ty ctorty
          pure $ (NormAbs sym ctor fty, fty)

        mkIndexTy' [] ((sym, ty) : ids) index args = do
          (ctor, ctorty) <- mkIndexTy' [] ids index (sym : args)
          pure $ (NormAbs sym ctor ctorty, ctorty)
          


typeCheck :: TIntermediate TIntermediate' -> Ctx.Context -> EvalM (TIntermediate Normal, Normal, Subst)
typeCheck expr ctx = case expr of
  (TValue v) -> do
    t <- liftExcept (typeVal v)
    pure (TValue v, t, nosubst)

  (TSymbol s) -> do
    case runExcept (Ctx.lookup s ctx) of 
      Right (_, ty) -> pure (TSymbol s, ty, nosubst)
      Left _ -> throwError ("couldn't find type of symbol " <> s)

  
  (TImplApply l r) -> do 
    (l', tl, substl) <- typeCheck l ctx
    (r', tr, substr) <- typeCheck r ctx
    substboth <- compose substl substr
    case tl of  
      NormImplProd var t1 t2 -> do
        (lapp, rapp, substcomb) <- constrain t1 tr 
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
        (_, app, substcomb) <- constrain t1 tr  
        let r'' = mkApp r' app
        subst <- compose substcomb substboth
        pure (TApply l' r'', t2, subst)
      NormProd var a t2 -> do 
        (_, app, substcomb) <- constrain a tr 
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
      deriveFn (NormImplProd var _ t2) tr r = do
        (args, unbnd, subst, rettype) <- deriveFn t2 tr r
        case findStrSubst var subst of 
          Just ty -> do
            retTy <- Eval.normSubst (ty, var) rettype
            pure (((True, (TValue ty)) : args),
                           unbnd,
                           rmSubst var subst,
                           retTy)
          Nothing -> pure ((True, TValue (Neu $ NeuVar var)) : args, ((NormUniv 0, var):unbnd),
                           rmSubst var subst, rettype)
      deriveFn (NormArr t1 t2) tr r = do
        (app, _, subst) <- constrain tr t1
        pure ([(False, mkApp r app)], [], subst, t2)
      deriveFn t tr r = do
        var' <- freshVar 
        (lapp, rapp, subst) <- constrain (NormArr tr var') t 
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
               Just ty -> (((BoundArg nme ty, isImpl) : args'), rmSubst ("#" <> show id) subst', impl)
               Nothing -> ((BoundArg nme (Neu (NeuVar ("#" <> show id))), isImpl) : args',
                           subst',
                           ("#" <> show id) : impl)

  (TProd (arg, bl) body) -> do
    case arg of  
      BoundArg var (TIntermediate' ty) -> do
        ty' <- evalTIntermediate ty ctx
        (body', bodyTy, subst) <- typeCheck body (Ctx.insert var (Neu $ NeuVar var) ty' ctx)
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
         
       
  (TIF cond e1 e2) -> do 
    (cond', tcond, substcond) <- typeCheck cond ctx
    (e1', te1, subste1) <- typeCheck e1 ctx
    (e2', te2, subste2) <- typeCheck e2 ctx
    (capp, _, substcnd') <- constrain tcond (PrimType BoolT)
    (lapp, rapp, substterms) <- constrain te1 te2

    let cond'' = mkApp cond' capp
        e1'' = mkApp e1' lapp
        e2'' = mkApp e2' rapp
    
    s1 <- compose substcond subste1 
    s2 <- compose s1 subste2 
    s3 <- compose s2 substcnd'
    s4 <- compose s3 substterms
    fnlTy <- doSubst s4 te1
    pure (TIF cond'' e1'' e2'', fnlTy, s4)

  (TStructure defs) -> do  
    let foldDefs :: [TDefinition TIntermediate'] -> Ctx.Context
                 -> EvalM ([TDefinition Normal], [(String, Normal)], Subst)
        foldDefs [] _ = pure ([], [], [])
        foldDefs (def : defs) ctx = do
          (def', var, val, subst) <- typeCheckDef def ctx
          (defs', fields, subst') <- foldDefs defs (Ctx.insert var (Neu $ NeuVar var) val ctx)
          fnlSubst <- compose subst subst'
          pure (def' : defs',  (var, val) : fields, fnlSubst)
          
    (defs', fields, subst) <- foldDefs defs ctx

    pure (TStructure defs', NormSig fields, subst)

  (TSignature defs) -> do  
    let foldDefs :: [TDefinition TIntermediate'] -> Ctx.Context
                 -> EvalM ([TDefinition Normal], [(String, Normal)], Subst)
        foldDefs [] _ = pure ([], [], [])
        foldDefs (def : defs) ctx = do
          (def', var, val, subst) <- typeCheckDef def ctx
          (defs', fields, subst') <- foldDefs defs (Ctx.insert var (Neu $ NeuVar var) val ctx)
          fnlSubst <- compose subst subst'
          pure (def' : defs',  (var, val) : fields, fnlSubst)
          
    (defs', fields, subst) <- foldDefs defs ctx

    pure (TSignature defs', NormUniv 0, subst)

  (TMatch term patterns) -> do
    (term', ty, subst) <- typeCheck term ctx
    retTy <- freshVar 
    (patterns', subst') <- checkPatterns patterns ty retTy
    outSubst <- compose subst subst'
    retTy' <- doSubst outSubst retTy
    let fnlSubst = rmSubst (show retTy) outSubst
    pure $ (TMatch term' patterns', retTy', fnlSubst)
    where
      -- Check Patterns: take a list of patterns as input, along with the
      -- matching type and return type, to be unified with
      -- return a pattern, the return type of that pattern and the required substituion
      checkPatterns :: [(TPattern TIntermediate', TIntermediate TIntermediate')] -> Normal -> Normal
                    -> EvalM ([(TPattern Normal, TIntermediate Normal)], Subst)
      checkPatterns [] _ _ = pure ([], nosubst)
      checkPatterns ((p, e) : ps) matchty retty = do
        -- get the type of 
        (p', matchty', ctxUpd) <- getPatternType p
        
  
        let ctx' = foldr (\(sym, ty) ctx -> Ctx.insert sym (Neu $ NeuVar sym) ty ctx) ctx ctxUpd
        (e', eret, esubst) <- typeCheck e ctx'

        -- TODO: ensure that the constrains are right way round...
        -- TODO: what to do with lapp1, lapp2 etc...
        (lapp1, rapp1, restMatchSubst) <- constrain matchty matchty'
        (lapp2, rapp2, restRetSubst) <- constrain retty eret
        (ps', pssubst) <- checkPatterns ps matchty retty
  
        -- TODO: make sure composition is right way round...
        substFnl <- composeList [restMatchSubst, restRetSubst, esubst, pssubst]
        pure $ ((p', e') : ps', substFnl)
      
      -- TODO: check for duplicate variable patterns!
      -- Get the type of a single pattern, to be constrained against.
      -- Also, return a list of variables and their
        
      getPatternType :: TPattern TIntermediate' -> EvalM (TPattern Normal, Normal, [(String, Normal)]) 
      getPatternType TWildPat = do
        var <- freshVar
        pure $ (TWildPat, var, [])
      getPatternType (TBindPat sym) = do
        ty <- freshVar
        pure $ (TBindPat sym, ty, [(sym, ty)])
      getPatternType (TIMatch indid altid (TIntermediate' altTy) subpatterns) = do 
        lst <- mapM getPatternType subpatterns
        let (subpatterns', norms, vars) = foldr (\(s, n, v) (ss, ns, vs) -> (s:ss, n:ns, v <> vs)) ([], [], []) lst 
        altTy' <- evalTIntermediate altTy ctx
        retty <- foldTyApp altTy' norms
        pure $ (TIMatch indid altid altTy' subpatterns', retty, vars)

        where 
          foldTyApp ty [] = pure ty
          foldTyApp ty (n : ns) = do
            ty' <- Eval.tyApp ty n
            foldTyApp ty' ns
      -- getPatternType (MatchModule fields) = do 



  other -> 
    throwError ("typecheck unimplemented for intermediate term " <> show other)

  where
    updateFromArgs :: Ctx.Context -> [(TArg TIntermediate', Bool)] -> EvalM (Ctx.Context, [(TArg Normal, Bool)])
    updateFromArgs ctx [] = pure (ctx, [])
    updateFromArgs ctx ((arg, bl) : args) = do 
      case arg of
        BoundArg str (TIntermediate' ty) -> do
          ty' <- evalTIntermediate ty ctx
          (ctx', args') <- updateFromArgs (Ctx.insert str (Neu $ NeuVar str) ty' ctx) args
          pure (Ctx.insert str (Neu $ NeuVar str) ty' ctx', ((BoundArg str ty', bl) : args'))
        InfArg str id -> do
          (ctx', args') <- updateFromArgs ctx args
          pure (Ctx.insert str (Neu $ NeuVar str) (Neu $ NeuVar ("#" <> show id))  ctx',
                               (InfArg str id, bl) : args')


typeCheckDef :: TDefinition TIntermediate' -> Ctx.Context
             -> EvalM (TDefinition Normal, String, Normal, Subst)
typeCheckDef (TSingleDef name body ty) ctx = do 
  bnd <- case ty of 
    Nothing -> freshVar
    Just (TIntermediate' ty) -> evalTIntermediate ty ctx
  (body', ty', subst) <- typeCheck body (Ctx.insert name (Neu $ NeuVar name) bnd ctx)
  pure (TSingleDef name body' (Just ty'), name, ty', subst)
typeCheckDef def _ = do
  throwError ("")



-- Constrain: similar to unification, but with significant enough differences
-- that I've renamed it for clarity. The differences are:
--   + Instead of t1[subst] = t2[subst], we have t1[subst] <: t2[subst]. 
--   + It returns a two list of applications l1, l2, which should be applied to
--     the corresponding in order which h

-- In constrainl(constrainr), we unify variables we are inferring (integers),
-- but the substitution of dependently-bound (string) variables occurs only on
-- the left(right) side

constrain :: Normal -> Normal -> EvalM ([Normal], [Normal], Subst)
constrain n1 n2 = do
  (lapp, rapp, subst) <- constrainLRApp n1 n2
  pure (lapp, rapp, toSing subst)


-- constrainLRApp :: Normal -> Normal -> EvalM ([Normal], [Normal], LRSubst)
-- TODO: If they are both an implicit apply, may need to re-abstract and
--   substitute in neutral variables (as done in TApply). For now, just move straight to constrain' 
-- TODO: we need to perform a renaming in variable-capturing forms, so that we can constrain, e.g.  
-- List [A] and {A} → List A by first renaming List [A] & {S} → List S then performing application
-- ({S} → List S) {A} to get List [A] and List [A]!!

constrainLRApp (NormImplProd s a b) (NormImplProd s' a' b') = do
  subst <- constrain' b b'
  pure ([], [], subst)
constrainLRApp (NormImplProd s a b) (Neu (NeuVar v)) = do
  if occurs v (NormImplProd s a b) then  
    err "occurs check failed"
  else 
    pure ([], [], rightsubst (NormImplProd s a b) v)
constrainLRApp (NormImplProd s a b)    r = do
  (a1, a2, subst) <- constrainLRApp b r
  appval <- case findLStrSubst s subst of  
    Just v -> pure v
    Nothing -> err ("cannot LRconstrain terms with different forms: "
                    <> show (NormImplProd s a b) <> " "
                    <> show r)
  pure ((appval:a1), a2, rmLSubst s subst)

  
constrainLRApp (Neu (NeuVar v))(NormImplProd s' a' b') = do
  if occurs v (NormImplProd s' a' b') then  
    err "occurs check failed"
  else 
    pure ([], [], leftsubst (NormImplProd s' a' b') v)
constrainLRApp l (NormImplProd s' a' b') = do
  (a1, a2, subst) <- constrainLRApp b' l
  appval <- case findRStrSubst s' subst of  
    Just v -> pure v
    Nothing -> err ("cannot LRconstrain terms with different forms: "
                    <> show l <> " "
                    <> show (NormImplProd s' a' b'))
  pure (a1, (appval:a2), rmRSubst s' subst)
constrainLRApp l r = do
  subst <- constrain' l r
  pure ([], [], subst)

  
constrain' :: Normal -> Normal -> EvalM LRSubst
constrain' (Neu (NeuVar v1)) (Neu (NeuVar v2)) =
    if v1 == v2 then pure lrnosubst
    else pure (rightsubst (Neu $ NeuVar v1) v2)
constrain' (Neu (NeuVar v)) ty =
  if occurs v ty then 
    err "occurs check failed"
  else
    pure (leftsubst ty v)
constrain' ty (Neu (NeuVar v)) =
  if occurs v ty then 
    err "occurs check failed"
  else
    pure (rightsubst ty v)
constrain' (PrimVal p1) (PrimVal p2) =
  if p1 == p2 then pure lrnosubst else err ("non-equal primitives in constrain: "
                                            <> show p1 <> " and " <> show p2)
constrain' (PrimType p1) (PrimType p2) =
  if p1 == p2 then pure lrnosubst else err ("non-equal primitives in constrain: "
                                            <> show p1 <> " and " <> show p2)
constrain' (NormUniv n1) (NormUniv n2) =
  if n1 == n2 then pure lrnosubst else err ("non-equal primitives in constrain"
                                            <> show (NormUniv n1) <> " and " <> show (NormUniv n2))

constrain' (NormArr l1 r1) (NormArr l2 r2) = do
  -- remember: function subtyping is contravaraiant in the argument and
  -- covariant in the return type
  s1 <- constrain' l2 l1
  s2 <- constrain' r1 r2
  composelr s1 s2

constrain' (NormProd str l1 r1) (NormProd str' l2 r2) =
  -- TODO: is dependent subtyping is contravaraiant in the argument and
  -- covariant in the return type
  if str == str' then do
    s1 <- constrain' l2 l1
    checkSubst "error: constrain attempting substitution for dependently bound type" str s1
    s2 <- constrain' r1 r2 
    composelr s1 s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain' (NormImplProd str l1 r1) (NormImplProd str' l2 r2) =
  -- TODO: same as above (dependent)
  if str == str' then do
    s1 <- constrain' l2 l1
    checkSubst "error: constrain attempting substitution for implicit dependently bound type" str s1
    s2 <- constrain' r1 r2 
    composelr s1 s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain' (NormSig m1) (NormSig m2) = 
  -- TODO: look out for binding of field-names to strings!!
  foldr (\(k, ty1) mnd ->
                      case getField k m2 of
                        Just ty2 -> do
                          s1 <- mnd
                          s2 <- constrain' ty1 ty2
                          composelr s1 s2 
                        Nothing -> err ("cannot constrain types, as rhs does not have field " <> k))
    (pure lrnosubst) m1

  
constrain' (NormSct m1) (NormSct m2) = 
  -- TODO: look out for binding of field-names to strings!!
  foldr (\(k, ty1) mnd ->
                      case getField k m2 of
                        Just ty2 -> do
                          s1 <- mnd
                          s2 <- constrain' ty1 ty2
                          composelr s1 s2 
                        Nothing -> err ("cannot constrain structures, as rhs does not have field " <> k))
    (pure lrnosubst) m1


constrain' (NormIVal name1 tyid1 id1 vals1 norm1) (NormIVal name2 tyid2 id2 vals2 norm2) =
  if tyid1 == tyid2 && id1 == id2 then
    foldr (\(n1, n2) mnd -> do
              s1 <- mnd
              s2 <- constrain' n1 n2
              composelr s1 s2)
      (pure lrnosubst) (zip vals1 vals2)
  else
    err "cannot constrain inductive values of non-equal constructors"

constrain' (NormIType name1 id1 vals1) (NormIType name2 id2 vals2) =
  if id1 == id2 then
    foldr (\(n1, n2) mnd -> do
              s1 <- mnd
              s2 <- constrain' n1 n2
              composelr s1 s2)
      (pure lrnosubst) (zip vals1 vals2)
  else
    err "cannot constrain inductive datatypes of non-equal constructors"
  

constrain' t1 t2 =   
  err ("cannot constrain terms " <> show t1 <> " and " <> show t2 <> " as they have different forms")



derive :: TIntermediate Normal -> Normal -> Subst -> EvalM (TIntermediate Normal, Normal, Subst)
derive tint (NormImplProd s t1 t2) subst = 
  case t1 of 
    (NormUniv 0) -> case findStrSubst s subst of 
      -- TODO: the toMls feels dodgy...
      Just ty -> do
        fnlTy <- Eval.normSubst (ty, s) t2
        pure (TImplApply tint (TValue ty), fnlTy, rmSubst s subst)
      Nothing -> throwError ("unable to find type substitution in type: " <> show (NormImplProd s t1 t2))
    (NormSig sig) -> 
      throwError "inference for signatures not implemented yet!"
    _ -> throwError ("implicit argument only supported for type Type and Signature, not for " <> show t1)
-- if not implicit application, ignore!
derive tint ty subst = pure (tint, ty, subst)

findStrSubst :: String -> Subst -> Maybe Normal
findStrSubst str ((ty, str') : ss) =
  if str == str' then Just ty
  else findStrSubst str ss
findStrSubst _ [] = Nothing

rmSubst :: String -> Subst -> Subst
rmSubst str ((ty, str') : ss)=
  if str == str' then rmSubst str ss
  else let ss' = rmSubst str ss in ((ty, str') : ss')
rmSubst str [] = []



findLStrSubst :: String -> LRSubst -> Maybe Normal
findLStrSubst str (_, l, _) = findStrSubst str l

findRStrSubst :: String -> LRSubst -> Maybe Normal
findRStrSubst str (_, _, r) = findStrSubst str r

rmLSubst :: String -> LRSubst -> LRSubst
rmLSubst str (s, l, r) = (s, rmSubst str l, r)

rmRSubst :: String -> LRSubst -> LRSubst
rmRSubst str (s, l, r) = (s, l, rmSubst str r)


-- Substitution Utilities  
-- recall 
-- Subst = (Map.Map Int Normal, Map.Map String Normal)
-- we need to be able to join and query these substitutions

nosubst :: Subst
nosubst = []

lrnosubst :: LRSubst
lrnosubst = ([], [], [])
leftsubst :: Normal -> String -> LRSubst
leftsubst ty s = ([], [(ty, s)], [])
rightsubst :: Normal -> String -> LRSubst
rightsubst ty s =  ([], [], [(ty, s)])


-- composition of substitutions: For HM substitutions, they are run in order,
-- while for the string-based substitutions, we don't know in what order they
-- are run
-- thus, to compose s1 with s2
-- 1: we apply all of s1's HM substitutions to s2
-- 2: we append  of s1's string substitutions to s2's string substitutions
compose :: Subst -> Subst -> EvalM Subst
  -- TODO SEEMS DODGY!!
compose str1 str2 = pure $ str1 <> str2
-- compose (s : ss, str1) (s2, str2) =
--   let iter :: (Normal, String) -> [(Normal, a)] -> EvalM [(Normal, a)]
--       iter s [] = pure []
--       iter s ((ty, vr) : ss) = do
--         ty' <- Type.normSubst s ty
--         tl <- iter s ss
--         pure $ (ty', vr) : tl
--   in do
--     -- perform substitution s within s2 
--     tl <- iter s s2 
--     compose (ss, str1) (s : tl)

composeList [] = pure nosubst
composeList (s:ss) = do
  cmp <- composeList ss
  compose s cmp

composelr :: LRSubst -> LRSubst -> EvalM LRSubst
composelr ([], l1, r1) (s2, l2, r2) = pure (s2, l1 <> l2, r1 <> r2)
composelr (s : ss, l1, r1) (s2, l2, r2) =
  let iter :: (Normal, String) -> [(Normal, a)] -> EvalM [(Normal, a)]
      iter s [] = pure []
      iter s ((ty, vr) : ss) = do
        hd <- Eval.normSubst s ty
        tl <- iter s ss
        pure $ (hd, vr) : tl
  in do
    s2' <- iter s s2
    l2' <- iter s l2
    r2' <- iter s r2
    -- perform substitution s within s2 
    composelr (ss, l1, r1) (s : s2', l2', r2)

-- convert a lr substitution to a single substitution
-- TODO: this is BAD - we need to check for redundancy!
toSing  :: LRSubst -> Subst
toSing (s, left, right) = (s <> left <> right)

-- Perform substitution
-- TODO: do what about order of string substitution? rearranging??
doSubst :: Subst -> Normal  -> EvalM Normal 
doSubst subst ty = case subst of 
  [] -> pure ty 
  ((sty, s) : ss) -> do
    ty' <- Eval.normSubst (sty, s) ty
    doSubst ss ty'

-- Throw an error if a variable (string) is contained in a substitution
checkSubst :: String -> String -> LRSubst -> EvalM ()
checkSubst msg str (_, l, r) = checkSubst' str (l <> r)
  where
    checkSubst' _ [] = pure ()
    checkSubst' str ((ty, str') : ss) = 
      if str == str' then 
        err msg
      else 
        checkSubst' str ss
      


-- Apply a term to a list of normal values
mkApp :: TIntermediate Normal -> [Normal] -> TIntermediate Normal
mkApp term [] = term
mkApp term (v:vs) = mkApp (TApply term (TValue v)) vs

tyApp :: Normal -> [Normal] -> EvalM Normal
tyApp ty [] = pure ty
tyApp (NormArr l r) (v:vs) = tyApp r vs
tyApp (NormProd s a b) (v:vs) = Eval.normSubst (v, s) b >>= (\n -> tyApp n vs)
tyApp (NormImplProd s a b) (v:vs) = Eval.normSubst (v, s) b >>= (\n -> tyApp n vs)

  
-- TODO: we need to shadow bound variables!!
-- Occurs Check: given a variable x and a type t, x occurs in t 
-- if some subterm of t is equal to x and x is not equal to t
occurs :: String -> Normal -> Bool
occurs _ (Neu (NeuVar _)) = False
occurs v t = occurs' v t

-- OccursCheck': Subtly different from occurs, this algorithm is recursive:
-- occurs' is true for variable v and type t if v = t or occurs' is
-- true for v any subterms in t
occurs' :: String -> Normal -> Bool
  -- Primitive types and values
occurs' _ (NormUniv _) = False
occurs' _ (PrimType _) = False
occurs' _ (PrimVal _) = False

  -- Builtin compound types (arrays, etc.)
occurs' v (NormArrTy ty) = occurs' v ty

occurs' v1 (Neu neu) = occursNeu v1 neu
occurs' v (NormArr t1 t2) = occurs' v t1 || occurs' v t2
occurs' v (NormProd str t1 t2) = -- remember: dependent type binding can shadow!
  if v == str then
    occurs' v t1
  else
    occurs' v t1 || occurs' v t2
occurs' v (NormImplProd str t1 t2) = -- remember: dependent type binding can
  -- shadow!
  if v == str then
    occurs' v t1
  else
    occurs' v t1 || occurs' v t2

occurs' v (NormSig fields) = foldr (\(_, ty) b -> b || occurs' v ty) False fields
occurs' v (NormSct fields) = foldr (\(_, ty) b -> b || occurs' v ty) False fields

occurs' v (NormIType _ _ params) = foldr (\ty b -> b || occurs' v ty) False params
occurs' v (NormIVal _ _ _ params _) = -- TODO: check if we need to ask about free vars in the type??
  foldr (\ty b -> b || occurs' v ty) False params


occursNeu :: String -> Neutral -> Bool   
occursNeu v1 (NeuVar v2) = v1 == v2
occursNeu v (NeuApp l r) = occursNeu v l || occurs' v r
occursNeu v (NeuDot m _) = occursNeu v m
occursNeu v (NeuIf c e1 e2) = occursNeu v c || occurs' v e1 || occurs' v e2

  
freshVar :: EvalM Normal  
freshVar = do
  id <- use var_counter 
  var_counter += 1
  pure (Neu $ NeuVar ("#" <> show id))


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
