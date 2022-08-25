module Typecheck.Typecheck where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except (runExcept)
import Control.Monad.State 
-- import Control.Lens 

import Data (PrimType(..),
             TypeNormal(..),
             TypeExpr(..),
             TypeNormal(..),
             TypeNeutral(..),
             Value(Type),
             var_counter,
             EvalM)
import Syntax.TIntermediate

import qualified Typecheck.Context as Ctx
import qualified Interpret.Type as Type
import qualified Interpret.Environment as Env
import Interpret.EvalM
import Typecheck.TypeUtils (typeVal, free, getField)

 -- TODO: check - types are expressions, or values ?!?


--   
type LRSubst = ([(TypeNormal, String)], [(TypeNormal, String)], [(TypeNormal, String)])
type Subst = [(TypeNormal, String)]
-- type TypeM = ExceptT String (State Int)

err = throwError  
-- runCheckerTop :: TIntTop TypeNormal -> Ctx.Context
--               -> Either String (Either (TIntTop TypeNormal, TypeNormal) (TIntTop TypeNormal))
-- runCheckerTop term env = 
--   let mnd = do 
--         res <- typeCheckTop term env
--         case res of 
--           Left (infterm, inftype) -> do
--             let term' = coalesceTop infterm
--                 ty' = toMls inftype
--             pure (Left (term', ty'))
--           Right infterm -> do
--             let term' = coalesceTop infterm
--             pure (Right term')

--   in 
--     case runState (runExceptT mnd) 0 of 
--       (Left err, _) -> Left err
--       (Right val, _) -> Right val
  

-- runChecker :: TIntermediate TypeExpr -> Ctx.Context -> Either String (TIntermediate TypeNormal, TypeNormal)
-- runChecker term env = 
--   let mnd :: EvalM (TIntermediate TypeNormal, TypeNormal)
--       mnd  = do 
--         (infterm, ty, subst) <- typeCheck term env
--         if subst /= nosubst then
--           throwError "substitution not empty at conclusion of type-checking!!"
--         else
--           pure (term, ty)
--   in 
--     case runState (runExceptT mnd) 0 of 
--       (Left err, _) -> Left err
--       (Right val, _) -> Right val


typeCheckTop :: TIntTop TypeExpr -> Ctx.Context
             -> EvalM (Either (TIntTop TypeNormal, TypeNormal) (TIntTop TypeNormal))
typeCheckTop (TExpr e) env = do
      (expr, ty, subst) <- typeCheck e env
      -- (expr', ty') <- buildDepFn expr ty
      pure $ Left $ (TExpr expr, ty)

typeCheckTop (TDefinition def) env = 
  case def of 
    TSingleDef name expr Nothing -> do
      (expr', ty, subst) <- typeCheck expr env
      if subst == []
        then 
          throwError "subst strings empty at toplevel!"
        else do
          -- (expr'', ty') <- buildDepFn expr' ty
          pure $ Right $ TDefinition $ TSingleDef name expr' (Just ty)

    TSingleDef name expr (Just mty) -> do
      throwError "cannot check type-annotated single definitions"

    TOpenDef expr Nothing -> do 
      (expr', ty, subst) <- typeCheck expr env
      if subst /= nosubst
        then 
          throwError "subst non-empty at toplevel!"
        else
          pure $ Right $ TDefinition $ TOpenDef expr' (Just ty)

--     TVariantDef nme params id alrs ty -> 
--       -- TODO: check for well-formedness!! (maybe?)
--       pure $ Right $ TDefinition $ TVariantDef nme params id (map (\(n, i, ts) -> (n, i, map toInf ts)) alrs)
--                      (toInf ty)

--     -- TEffectDef  String [String] Int [(String, Int, [TypeNormal])]

-- buildDepFn :: (TIntermediate TypeNormal) -> TypeNormal -> EvalM (TIntermediate TypeNormal, TypeNormal)
-- buildDepFn expr ty = do
--   let bothFree = Set.toList (free ty)
--   freeVars <- mapM (\str -> throwError ("non-inference type variable free when building Dependent Fn "
--                                     <> str <> " in type " <> show ty <> " for val " <> show expr)) 
--           bothFree
--   let --mkFunTy :: []
--       mkFunTy [] ty = ty
--       mkFunTy (id : ids) ty = NormImplDep ("#" <> show id) (NormUniv 0) (mkFunTy ids ty)
--       mkFun [] bdy = bdy
--       mkFun vars bdy =
--         TLambda (map (\id -> (BoundArg ("#" <> show id) (NormUniv 0), True)) vars)
--                 bdy
--                 (Just (mkFunTy freeVars ty))
--   pure (mkFun freeVars expr, mkFunTy freeVars ty)
        

typeCheck :: TIntermediate TypeExpr -> Ctx.Context -> EvalM (TIntermediate TypeNormal, TypeNormal, Subst)
typeCheck expr ctx = case expr of
  (TValue v) -> do
    t <- liftExcept (typeVal v)
    pure (TValue v, t, nosubst)

  (TSymbol s) -> do
    case runExcept (Ctx.lookup s ctx) of 
      Right (Left ty) -> pure (TSymbol s, ty, nosubst)
      Right (Right (_, ty)) -> pure (TSymbol s, ty, nosubst)
      Left err -> throwError ("couldn't find type of symbol " <> s)

  (TApply l r) -> do 
    (l', tl, substl) <- typeCheck l ctx
    (r', tr, substr) <- typeCheck r ctx
    substboth <- compose substl substr
    case tl of  
      NormArr t1 t2 -> do 
        substcomb <- constrain tr t1 
        let substsing = toSing substcomb
        subst <- compose substsing substboth
        pure (TApply l' r', t2, subst)
      NormDep var t1 t2 -> do 
        substcomb <- constrain tr t1 
        let substsing = toSing substcomb
        subst <- compose substsing substboth

        -- convert r' to a literal type (int/int → int etc.), then apply it to
        -- the (dependent) closure. 
        -- in the future, r' should also be able to be a context variable, not
        -- just a literal value! 
        appTy <- toDepLiteral r' ctx
        retTy <- Type.normSubst (appTy, var) t2
        pure (TApply l' r', retTy, subst)
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
      deriveFn :: TypeNormal -> TypeNormal -> TIntermediate TypeNormal
               -> EvalM ([(Bool, TIntermediate TypeNormal)], [(TypeNormal, String)], Subst, TypeNormal)
      deriveFn (NormImplDep var (NormUniv 0) t2) tr r = do
        (args, unbnd, subst, rettype) <- deriveFn t2 tr r
        case findStrSubst var subst of 
          Just ty -> do
            retTy <- Type.normSubst (ty, var) rettype
            pure (((True, (TType ty)) : args),
                           unbnd,
                           rmSubst var subst,
                           retTy)
          Nothing -> pure ((True, TType (Neu $ NeuVar var)) : args, ((NormUniv 0, var):unbnd),
                           rmSubst var subst, rettype)
      deriveFn (NormArr t1 t2) tr r = do
        substlr <- constrain tr t1
        let subst = toSing substlr
        pure ([(False, r)], [], subst, t2)
      deriveFn t tr r = do
        var' <- freshVar 
        substlr <- constrain t (NormArr tr var')
        let subst = toSing substlr
        pure ([(False, r)], [], subst, var')

      mkFnlFn :: [(Bool, TIntermediate TypeNormal)] -> [(TypeNormal, String)] -> TIntermediate TypeNormal -> TypeNormal
              -> (TIntermediate TypeNormal, TypeNormal)
      mkFnlFn args unbound bdy bodyty = (fnlfn, fnlty)
        where
          fnlfn :: TIntermediate TypeNormal
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
          fnlty :: TypeNormal
          fnlty =
            case unbound of 
              [] -> bodyty -- TODO: eval bodyty if empty
              ((ty, var) : xs) -> NormImplDep var ty (mkFnlBdy xs bodyty)
          mkFnlBdy :: [(TypeNormal, String)] -> TypeNormal -> TypeNormal
          mkFnlBdy [] ret = ret
          mkFnlBdy ((ty, var) : xs) ret = NormImplDep var ty (mkFnlBdy xs ret) 
          

  (TLambda args body mty) -> do 
     (ctx', args') <- updateFromArgs ctx args
     (body', ty, subst) <- typeCheck body ctx'
     case mty of 
       Nothing -> do
         let fnlArgs = fixArgs args' subst
         fnlTy <- buildFnType fnlArgs subst ty
         let fnl_lambda = TLambda fnlArgs body' (Just fnlTy)
         pure (fnl_lambda, fnlTy, subst)
       -- TODO: add checking if lambda type already there...

     where 
       buildFnType :: [(TArg TypeNormal, Bool)] -> Subst -> TypeNormal -> EvalM TypeNormal 
       buildFnType [] _ bodyty = pure bodyty
       -- TODO: consider substitutions!
       buildFnType ((ty, bl):tys) subst bodyty = do
         ret_ty <- buildFnType tys subst bodyty
         case ty of 
           BoundArg str t -> if bl then  
             pure (NormImplDep str t ret_ty)
             else pure (NormDep str t ret_ty)
           InfArg _ _ -> 
             throwError "buildFnType not expecting inference!"

       -- fixArgs will take a list of Typed arguments, and convert any
       -- inference arguments to string arguments
       fixArgs :: [(TArg TypeNormal, Bool)] -> Subst -> [(TArg TypeNormal, Bool)]
       fixArgs [] subst = []  
       fixArgs ((arg, impl) : args) subst = case arg of  
         BoundArg str ty -> (BoundArg str ty, impl) : fixArgs args subst
         -- TOOD: come up with a better solution to new names...
         InfArg nme id -> case findStrSubst ("#" <> show id) subst of 
           Just ty -> (BoundArg nme ty, impl) : fixArgs args subst
           Nothing -> (BoundArg nme (NormUniv 0), impl) : fixArgs args subst

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
    substcnd' <- constrain tcond (NormPrim BoolT)
    substterms <- constrain te1 te2
    let substcnd'' = toSing substcnd'
        substterms' = toSing substterms
    
    s1 <- compose substcond subste1 
    s2 <- compose s1 subste2 
    s3 <- compose s2 substcnd''
    s4 <- compose s3 substterms'
    fnlTy <- dosubst s4 te1
    pure (TIF cond' e1' e2', fnlTy, s4)

  -- TODO: mutually recursive definitions...
  (TModule defs) -> do  
    result <- mapM (\int -> typeCheckDef int ctx) defs
    -- extract different values from the result   
    let defs' = map (\(def, _, _, _) -> def) result
        sig = map (\(_, str, ty, _) -> (str, ty)) result

        foldCmp mnd [] = mnd
        foldCmp mnd (s:ss) = do
          s' <- mnd
          foldCmp (compose s s') ss

    subst <- foldCmp (pure nosubst) (map (\(_, _, _, subst) -> subst) result)

    pure (TModule defs', NormSig sig, subst)

    


  other -> 
    throwError ("typecheck unimplemented for intermediate term " <> show other)

  where
    updateFromArgs :: Ctx.Context -> [(TArg TypeExpr, Bool)] -> EvalM (Ctx.Context, [(TArg TypeNormal, Bool)])
    updateFromArgs ctx [] = pure (ctx, [])
    updateFromArgs ctx ((arg, bl) : args) = do 
      (ctx', args') <- updateFromArgs ctx args
      case arg of
        BoundArg str ty -> do
          ty' <- local (Ctx.ctxToEnv ctx) (Type.eval ty)
          pure (Ctx.insert str ty' ctx', ((BoundArg str ty', bl) : args'))
        InfArg str id -> pure (Ctx.insert str (Neu $ NeuVar ("#" <> show id)) ctx',
                               (InfArg str id, bl) : args')


typeCheckDef :: TDefinition TypeExpr -> Ctx.Context
             -> EvalM (TDefinition TypeNormal, String, TypeNormal, Subst)
-- typeCheckDef (TVariantDef name vars id variants ty)
-- typeCheckDef (TEffectDef  name vars id actions)
typeCheckDef (TSingleDef name body ty) ctx = do 
  bnd <- case ty of 
    Nothing -> freshVar
    Just ty -> local (Ctx.ctxToEnv ctx) (Type.eval ty)
  (body', ty', subst) <- typeCheck body (Ctx.insert name bnd ctx)
  pure (TSingleDef name body' (Just ty'), name, ty', subst)


-- typeCheckDef (TOpenDef body ty)


-- constrain: like unify, but instead of t1[subst] = t2[subst], we have
-- t1[subst] <: t2[subst] 

-- In constrainl(constrainr), we unify variables we are inferring (integers),
-- but the substitution of dependently-bound (string) variables occurs only on
-- the left(right) side

-- TODO: break down constrain so that we have a "top" constrain that can
-- instantiate either left or right implicit dependent products?  
-- TODO: perhaps this needs to be done at any level (not just the top?)
constrain :: TypeNormal -> TypeNormal -> EvalM LRSubst
constrain (Neu (NeuVar v1)) (Neu (NeuVar v2)) =
    if v1 == v2 then pure lrnosubst
    else pure (rightsubst (Neu $ NeuVar v1) v2)
constrain (Neu (NeuVar v)) ty =
  if occurs v ty then 
    err "occurs check failed"
  else
    pure (leftsubst ty v)
constrain ty (Neu (NeuVar v)) =
  if occurs v ty then 
    err "occurs check failed"
  else
    pure (rightsubst ty v)
constrain (NormPrim p1) (NormPrim p2) =
  if p1 == p2 then pure lrnosubst else err ("non-equal primitives in constrain: "
                                            <> show p1 <> " and " <> show p2)
constrain (NormUniv n1) (NormUniv n2) =
  if n1 == n2 then pure lrnosubst else err ("non-equal primitives in constrain"
                                            <> show (NormUniv n1) <> " and " <> show (NormUniv n2))

constrain (NormArr l1 r1) (NormArr l2 r2) = do
  -- remember: function subtyping is contravaraiant in the argument and
  -- covariant in the return type
  s1 <- constrain l2 l1
  s2 <- constrain r1 r2
  composelr s1 s2

constrain (NormDep str l1 r1) (NormDep str' l2 r2) =
  -- TODO: is dependent subtyping is contravaraiant in the argument and
  -- covariant in the return type
  if str == str' then do
    s1 <- constrain l2 l1
    checkSubst "error: constrain attempting substitution for dependently bound type" str s1
    s2 <- constrain r1 r2 
    composelr s1 s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain (NormImplDep str l1 r1) (NormImplDep str' l2 r2) =
  -- TODO: same as above (dependent)
  if str == str' then do
    s1 <- constrain l2 l1
    checkSubst "error: constrain attempting substitution for implicit dependently bound type" str s1
    s2 <- constrain r1 r2 
    composelr s1 s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain (NormSig m1) (NormSig m2) = 
  -- TODO: look out for binding of field-names to strings!!
  foldr (\(k, ty1) mnd ->
                      case getField k m2 of
                        Just ty2 -> do
                          s1 <- mnd
                          s2 <- constrain ty1 ty2
                          composelr s1 s2 
                        Nothing -> err ("cannot constrain types, as rhs does not have field" <> k))
    (pure lrnosubst) m1

-- TODO: what if the type in field is transparent? is it evaluated away?
-- constrain (NormDot t1 field1) (TyDot t2 field2) = 
--   if field1 == field2 then 
--     constrain t1 t2
--   else 
--     err ("cannot constrain type" <> show t1 <> " and " <> show t2 <> " as they access different fields")


-- TOOD: IMNamed/IMEffect 
-- constrain (IMNamed id1 name1 params1 instances1) (IMNamed id2 name2 params2 instances2) = 

-- constrain (IMEffect set1 rettype1) (IMEffect set2 rettype2) = 
--   s1 <- (\ty mnd -> do
--             s1 <- mnd
--             s2 <- tryConstraint ty set2
--             compose s1 s2) set1
--   s2 <- constrain rettype1 rettype2
--   compose s1 s2

--   where
--     -- Note: as a consistency/constraint, we require that each effect type appears
--     -- only once in the set, even if it has different arguments! 
--     -- TODO: how does subtyping work for instanced effects: sometimes a type is
--     -- an argument, sometimes returned!! 
--     tryConstraint (CustomEff id tys) set = 
--       Set.filter (\t -> case t of
--                      (CustomEff id' tys' -> )
--                      )


constrain (NormVector ty1) (NormVector ty2) = constrain ty1 ty2

constrain t1 t2 =   
  err ("cannot constrain types" <> show t1 <> " and " <> show t2 <> " as they have different forms")

-- toTypeNormal :: TypeNormal -> TypeNormal 



-- Implicit argument inference  
deriveLeft :: TIntermediate TypeNormal -> TypeNormal -> LRSubst -> EvalM (TIntermediate TypeNormal, TypeNormal, LRSubst)
deriveLeft tinf ty (s, l, r) = do
  (tinf', ty,  l') <- derive tinf ty l
  pure (tinf', ty, (s, l', r))
deriveRight :: TIntermediate TypeNormal -> TypeNormal -> LRSubst -> EvalM (TIntermediate TypeNormal, TypeNormal, LRSubst)
deriveRight tinf ty (s, l, r) = do
  (tinf', ty, r') <- derive tinf ty r
  pure (tinf', ty, (s, l, r'))

derive :: TIntermediate TypeNormal -> TypeNormal -> Subst -> EvalM (TIntermediate TypeNormal, TypeNormal, Subst)
derive tint (NormImplDep s t1 t2) subst = 
  case t1 of 
    (NormUniv 0) -> case findStrSubst s subst of 
      -- TODO: the toMls feels dodgy...
      Just ty -> do
        fnlTy <- Type.normSubst (ty, s) t2
        pure (TImplApply tint (TType ty), fnlTy, rmSubst s subst)
      Nothing -> throwError ("unable to find type substitution in type: " <> show (NormImplDep s t1 t2))
    (NormSig sig) -> 
      throwError "inference for signatures not implemented yet!"
    _ -> throwError ("implicit argument only supported for type Type and Signature, not for " <> show t1)
-- if not implicit application, ignore!
derive tint ty subst = pure (tint, ty, subst)

findStrSubst :: String -> Subst -> Maybe TypeNormal
findStrSubst str ((ty, str') : ss) =
  if str == str' then Just ty
  else findStrSubst str ss
findStrSubst _ [] = Nothing

rmSubst :: String -> Subst -> Subst
rmSubst str ((ty, str') : ss)=
  if str == str' then rmSubst str ss
  else let ss' = rmSubst str ss in ((ty, str') : ss')
rmSubst str [] = []


-- Substitution Utilities  
-- recall 
-- Subst = (Map.Map Int TypeNormal, Map.Map String TypeNormal)
-- we need to be able to join and query these substitutions

nosubst :: Subst
nosubst = []

lrnosubst :: LRSubst
lrnosubst = ([], [], [])
leftsubst :: TypeNormal -> String -> LRSubst
leftsubst ty s = ([], [(ty, s)], [])
rightsubst :: TypeNormal -> String -> LRSubst
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
--   let iter :: (TypeNormal, String) -> [(TypeNormal, a)] -> EvalM [(TypeNormal, a)]
--       iter s [] = pure []
--       iter s ((ty, vr) : ss) = do
--         ty' <- Type.normSubst s ty
--         tl <- iter s ss
--         pure $ (ty', vr) : tl
--   in do
--     -- perform substitution s within s2 
--     tl <- iter s s2 
--     compose (ss, str1) (s : tl)


composelr :: LRSubst -> LRSubst -> EvalM LRSubst
composelr ([], l1, r1) (s2, l2, r2) = pure (s2, l1 <> l2, r1 <> r2)
composelr (s : ss, l1, r1) (s2, l2, r2) =
  let iter :: (TypeNormal, String) -> [(TypeNormal, a)] -> EvalM [(TypeNormal, a)]
      iter s [] = pure []
      iter s ((ty, vr) : ss) = do
        hd <- Type.normSubst s ty
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
dosubst :: Subst -> TypeNormal  -> EvalM TypeNormal 
dosubst subst ty = case subst of 
  [] -> pure ty 
  ((sty, s) : ss) -> do
    ty' <- Type.normSubst (sty, s) ty
    dosubst ss ty'

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
      

  
-- Occurs Check: given a variable x and a type t, x occurs in t 
-- if some subterm of t is equal to x and x is not equal to t
occurs :: String -> TypeNormal -> Bool
occurs _ (Neu (NeuVar _)) = False
occurs v t = occurs' v t

-- OccursCheck': Subtly different from occurs, this algorithm is recursive:
-- occurs' is true for variable v and type t if v = t or occurs' is
-- true for v any subterms in t
occurs' :: String -> TypeNormal -> Bool
occurs' _ (NormUniv _) = False
occurs' _ (NormPrim _) = False
occurs' v1 (Neu (NeuVar v2)) = v1 == v2
occurs' v (NormSig sig) = foldr (\(_, ty) b -> b || occurs' v ty) False sig
occurs' v (NormArr t1 t2) = occurs' v t1 || occurs' v t2
occurs' v (NormDep str t1 t2) = -- remember: dependent type binding can shadow!
  if v == str then
    occurs' v t1
  else
    occurs' v t1 || occurs' v t2
occurs' v (NormImplDep str t1 t2) = -- remember: dependent type binding can
  -- shadow!
  if v == str then
    occurs' v t1
  else
    occurs' v t1 || occurs' v t2
occurs' v (NormVector ty) = occurs' v ty

  

-- MISC TYPE UTILS
-- toDepLiteral: given a value, convert to literal
-- + if it is a type return that type
-- + if it is a module, return the (literal) value of that module
-- + if it is a symbol (string: s) and has type Type type, return (Neu $ NeuVar a)
-- + if it is a non-type value, error!
-- + if application, error! (TODO: evaluate if pure!)
-- Intended to be used so arguments to 'dependent' functions can be converted
-- into types, and then substituted in to make sure it all works!
toDepLiteral :: TIntermediate TypeNormal -> Ctx.Context -> EvalM TypeNormal
toDepLiteral (TValue (Type t)) env = pure t
toDepLiteral (TType ty) env = pure ty
toDepLiteral e env = throwError ("non-type expression given to toDepLiteral: " <> show e)
-- toDepLiteral (TSymbol str)

freshVar :: EvalM TypeNormal  
freshVar = do
  id <- use var_counter 
  var_counter += 1
  pure (Neu $ NeuVar ("#" <> show id))
