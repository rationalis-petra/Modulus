module Typecheck.Typecheck where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except 
import Control.Monad.State 
import Control.Lens

import Data (EffectType(..),
             PrimType(..),
             ModulusType(..))
import Syntax.TIntermediate

import qualified Typecheck.Environment as Env
import Typecheck.InfType
import Typecheck.TypeUtils (typeExpr, toInf, toMls)

type LRSubst = ([(InfType, Int)], [(InfType, String)], [(InfType, String)])
type Subst = ([(InfType, Int)], [(InfType, String)])
type TypeM = ExceptT String (State Int)

err = throwError  

runCheckerTop :: TIntTop ModulusType -> Env.CheckEnv
              -> Either String (Either (TIntTop ModulusType, ModulusType) (TIntTop ModulusType))
runCheckerTop term env = 
  let mnd = do 
        res <- typeCheckTop term env
        case res of 
          Left (infterm, inftype) -> do
            let term' = coalesceTop infterm
                ty' = toMls inftype
            pure (Left (term', ty'))
          Right infterm -> do
            let term' = coalesceTop infterm
            pure (Right term')

  in 
    case runState (runExceptT mnd) 0 of 
      (Left err, _) -> Left err
      (Right val, _) -> Right val
  

runChecker :: TIntermediate ModulusType -> Env.CheckEnv
           -> Either String (TIntermediate ModulusType, ModulusType)
runChecker term env = 
  let mnd = do 
        (infterm, ty, subst) <- typeCheck term env
        if subst /= nosubst then
          throwError "substitution not empty at conclusion of type-checking!!"
          else pure ()
        let ty' = toMls ty
        let term' = coalesce infterm
        pure (term', ty')
  in 
    case runState (runExceptT mnd) 0 of 
      (Left err, _) -> Left err
      (Right val, _) -> Right val


typeCheckTop :: TIntTop ModulusType -> Env.CheckEnv
             -> TypeM (Either (TIntTop InfType, InfType) (TIntTop InfType))
typeCheckTop (TExpr e) env = (Left . (\(x, y, z) -> (TExpr x, y))) <$> typeCheck e env
typeCheckTop (TDefinition def) env = 
  case def of 
    TSingleDef name expr Nothing -> do
      (expr', ty, subst) <- typeCheck expr env
      if subst /= nosubst
        then 
          throwError "subst non-empty at toplevel!"
        else
          pure $ Right $ TDefinition $ TSingleDef name expr' (Just ty)

    TSingleDef name expr (Just mty) -> do
      throwError "cannot check type-annotated single definitions"
      -- (expr', ty) <- typeCheck expr env
      -- inf <- toInf mty
      -- checkEq ty mty'
      -- pure $ Right $ TDefinition $ TSingleDef name expr' (Just mty)

    TOpenDef expr Nothing -> do 
      (expr', ty, subst) <- typeCheck expr env
      if subst /= nosubst
        then 
          throwError "subst non-empty at toplevel!"
        else
          pure $ Right $ TDefinition $ TOpenDef expr' (Just ty)

    TVariantDef nme params id alrs ty -> 
      -- TODO: check for well-formedness!! (maybe?)
      pure $ Right $ TDefinition $ TVariantDef nme params id (map (\(n, i, ts) -> (n, i, map toInf ts)) alrs)
                     (toInf ty)

    -- TEffectDef  String [String] Int [(String, Int, [ModulusType])]

  


typeCheck :: TIntermediate ModulusType -> Env.CheckEnv -> TypeM (TIntermediate InfType, InfType, Subst)
typeCheck expr env = case expr of
  (TValue v) -> do
    case runExcept (typeExpr v) of 
      Right t -> pure (TValue v, toInf t, nosubst)
      Left err -> throwError err

  (TSymbol s) -> do
    case runExcept (Env.lookup s env) of 
      Right ty -> pure (TSymbol s, ty, nosubst)
      Left err -> throwError ("couldn't find type of " <> s)

  (TApply l r) -> do 
    (l', tl, substl) <- typeCheck l env
    (r', tr, substr) <- typeCheck r env
    substboth <- compose substl substr
    case tl of  
      IMArr t1 t2 -> do 
        substcomb <- constrain tr t1 
        let substsing = toSing substcomb
        subst <- compose substsing substboth
        pure (TApply l' r', t2, subst)
      other -> throwError (show other <> " is not a function type") 

  -- (TLambda args body mty) -> do 
  --    -- env' <- updateFromargs env args
  --    -- (body', ty, subst) <- typeCheck body env 
  --    -- case mty of 
  --    --   Nothing -> do
  --    --     fnl_ty <- buildFnType args subst ty  
  --    --     let fnl_args = fixArgs args subst  
  --    --         fnl_lambda = TLambda fnl_args body' (Just ty)
  --    --     pure (fnl_lambda, fnl_ty, subst)

     -- where 
     --   -- TODO: consider substitutions!
     --   buildFnType ((ty, bl):tys) subst bodyty = do
     --     ret_ty <- buildFnType tys subst bodyty
     --     case ty of 
     --       BoundArg str t -> if bl then  
     --         pure (IMImplDep t str ret_ty )
     --         else pure (IMDep t str ret_ty)
     --       ValArg str t -> if bl then 
     --         throwError "non-dependent arg cannot be implicit!"
     --         else pure (IMArr t ret_ty)
     --       -- InfArg str id -> if bl then 
     --       --   throwError "non-dependent arg cannot be implicit!"
     --       --   else IMArr t ret_ty 
     --   buildFnType [] _ bodyty = pure bodyty
  (TAccess term field) -> do
    (term', ty, subst) <- typeCheck term env 
    -- TODO: what if there is a substituion 
    case ty of 
      (IMSig map) -> case Map.lookup field map of 
        Just ty -> pure (TAccess term' field, ty, subst)
        Nothing -> throwError ("cannot find field " <> field)
      t -> throwError ("expected signature, got " <> show t)
         
       
  
  

  (TIF cond e1 e2) -> do 
    (cond', tcond, substcond) <- typeCheck cond env 
    (e1', te1, subste1) <- typeCheck e1 env 
    (e2', te2, subste2) <- typeCheck e2 env 
    substcnd' <- constrain tcond (IMPrim BoolT)
    substterms <- constrain te1 te2
    let substcnd'' = toSing substcnd'
        substterms' = toSing substterms
    
    s1 <- compose substcond subste1 
    s2 <- compose s1 subste2 
    s3 <- compose s2 substcnd''
    s4 <- compose s3 substterms'
    pure (TIF cond' e1' e2', dosubst s4 te1, s4)

  where
    updateFromArgs env [] = pure env
    updateFromArgs env ((arg, _) : args) = do 
      env' <- updateFromArgs env args
      case arg of
        BoundArg str ty -> pure (Env.insert str (toInf ty) env')
        ValArg str ty -> pure (Env.insert str (toInf ty) env')
        InfArg str id -> do pure (Env.insert str (IMVar (Right id)) env')

 --  TODO: add an implicit-application check at constraint points, so typechecks
 --  for any term can have implicit application!  


-- constrain: like unify, but instead of t1[subst] = t2[subst], we have
-- t1[subst] <: t2[subst] 

-- In constrainl(constrainr), we unify variables we are inferring (integers),
-- but the substitution of dependently-bound (string) variables occurs only on
-- the left(right) side
constrain :: InfType -> InfType -> TypeM LRSubst
constrain (IMVar v1) (IMVar v2) = case (v1, v2) of 
-- TODO: unioning variables: prioritise inference variable substitution, as is
-- outermost variable? outermost variable in general?
  (Right _, Left s) -> pure (rightsubst (IMVar v1) (Left s))
  (Left _, Right n) -> pure (rightsubst (IMVar v1) (Right n))
  (Left  s1, Left s2) ->
    if s1 == s2 then pure lrnosubst
    else pure (rightsubst (IMVar v1) (Left s2))
  (Right n1, Right n2) ->
    if n1 == n2 then pure lrnosubst
    else pure (rightsubst (IMVar v1) (Right n2))
constrain (IMVar v) ty =
  if occurs v ty then 
    err "occurs check failed"
  else
    pure (leftsubst ty v)
constrain ty (IMVar v) =
  if occurs v ty then 
    err "occurs check failed"
  else
    pure (rightsubst ty v)
constrain (IMPrim t1) (IMPrim t2) =
  if t1 == t2 then pure lrnosubst else err "non-equal primitives in constrain"
constrain (ITypeN n1) (ITypeN n2) =
  if n1 == n2 then pure lrnosubst else err "non-equal primitives in constrain"

constrain (IMArr l1 r1) (IMArr l2 r2) = do
  -- remember: function subtyping is contravaraiant in the argument and
  -- covariant in the return type
  s1 <- constrain l2 l1
  s2 <- constrain r1 r2
  composelr s1 s2

constrain (IMDep l1 str r1) (IMDep l2 str' r2) =
  -- TODO: is dependent subtyping is contravaraiant in the argument and
  -- covariant in the return type
  if str == str' then do
    s1 <- constrain l2 l1
    checkSubst "error: constrain attempting substitution for dependently bound type" str s1
    s2 <- constrain r1 r2 
    composelr s1 s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain (IMImplDep l1 str r1) (IMImplDep l2 str' r2) =
  -- TODO: same as above (dependent)
  if str == str' then do
    s1 <- constrain l2 l1
    checkSubst "error: constrain attempting substitution for implicit dependently bound type" str s1
    s2 <- constrain r1 r2 
    composelr s1 s2
  else
    err "cannot constrain dependent types with unequal arg"

constrain (IMSig m1) (IMSig m2) = 
  -- TODO: look out for binding of field-names to strings!!
  Map.foldrWithKey (\k ty1 mnd ->
                      case Map.lookup k m2 of 
                        Just ty2 -> do
                          s1 <- mnd
                          s2 <- constrain ty1 ty2
                          composelr s1 s2 
                        Nothing -> err ("cannot constrain types, as rhs does not have field" <> k))
    (pure lrnosubst) m1

-- TODO: what if the type in field is transparent? is it evaluated away?
constrain (IMDot t1 field1) (IMDot t2 field2) = 
  if field1 == field2 then 
    constrain t1 t2
  else 
    err ("cannot constrain type" <> show t1 <> " and " <> show t2 <> " as they access different fields")

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


constrain (IMVector ty1) (IMVector ty2) = constrain ty1 ty2

constrain t1 t2 =   
  err ("cannot constrain types" <> show t1 <> " and " <> show t2 <> " as they have different forms")


  
-- toInfType :: ModulusType -> InfType 







-- Substitution Utilities  
-- recall 
-- Subst = (Map.Map Int InfType, Map.Map String InfType)
-- we need to be able to join and query these substitutions

nosubst :: Subst
nosubst = ([], [])

lrnosubst :: LRSubst
lrnosubst = ([], [], [])
leftsubst :: InfType -> Either String Int -> LRSubst
leftsubst ty s = case s of
  Left str -> ([], [(ty, str)], [])
  Right n -> ([(ty, n)], [], [])
rightsubst :: InfType -> Either String Int -> LRSubst
rightsubst ty s = case s of
  Left str -> ([], [], [(ty, str)])
  Right n -> ([(ty, n)], [], [])

-- composition of substitutions: For HM substitutions, they are run in order,
-- while for the string-based substitutions, we don't know in what order they
-- are run
-- thus, to compose s1 with s2
-- 1: we apply all of s1's HM substitutions to s2
-- 2: we append  of s1's string substitutions to s2's string substitutions
compose :: Subst -> Subst -> TypeM Subst
compose ([], str1) (s2, str2) = pure (s2, str1 <> str2)
compose (s : ss, str1) (s2, str2) =
  let iter :: (InfType, Either String Int) -> [(InfType, a)] -> [(InfType, a)]
      iter s [] = []
      iter s ((ty, vr) : ss) = (substvar s ty, vr) : iter s ss

      s' = ((_2 %~ Right) s)
  in
    -- perform substitution s within s2 

    compose (ss, str1) (s : iter s' s2, iter s' str2)


composelr :: LRSubst -> LRSubst -> TypeM LRSubst
composelr ([], l1, r1) (s2, l2, r2) = pure (s2, l1 <> l2, r1 <> r2)
composelr (s : ss, l1, r1) (s2, l2, r2) =
  let iter :: (InfType, Either String Int) -> [(InfType, a)] -> [(InfType, a)]
      iter s [] = []
      iter s ((ty, vr) : ss) = (substvar s ty, vr) : iter s ss

      s' = ((_2 %~ Right) s)
  in
    -- perform substitution s within s2 

    composelr (ss, l1, r1) (s : iter s' s2, iter s' l2, iter s' r2)

-- convert a lr substitution to a single substitution
-- TODO: this is BAD - we need to check for redundancy!
toSing  :: LRSubst -> Subst
toSing (id, left, right) = (id, left <> right)

-- Perform substitution
-- TODO: do what about order of string substitution? rearranging??
dosubst :: Subst -> InfType  -> InfType 
dosubst subst ty = case subst of 
  ([], []) -> ty 
  ([], ((sty, s) : ss)) -> dosubst ([], ss) (substvar (sty, Left s) ty)
  (((sty, i) : ss), strs) -> dosubst (ss, strs) (substvar (sty, Right i) ty)

-- Perform substitution
lrdosubst :: LRSubst -> InfType  -> InfType 
lrdosubst subst ty = case subst of 
  ([], _, _) -> ty 
  (((sty, i) : ss), l, r) -> lrdosubst (ss, l, r) (substvar (sty, Right i) ty)
  
substvar :: (InfType, Either String Int) -> InfType -> InfType
substvar (ty, var) term = 
  case term of 
    IMVar var' -> if var == var' then ty else term
    IMArr t1 t2 -> 
      IMArr (substvar (ty, var) t1) (substvar (ty, var) t1)
    IMDep t1 s t2 -> case var of 
      Left str ->
        if str == s then 
          IMDep (substvar (ty, var) t1) s t2
        else
          IMDep (substvar (ty, var) t1) s (substvar (ty, var) t2)
      _ ->
        IMDep (substvar (ty, var) t1) s (substvar (ty, var) t2)
    IMImplDep t1 s t2 -> case var of 
      Left str ->
        if str == s then 
          IMImplDep (substvar (ty, var) t1) s t2
        else
          IMImplDep (substvar (ty, var) t1) s (substvar (ty, var) t2)
      _ ->
        IMImplDep (substvar (ty, var) t1) s (substvar (ty, var) t2)
    IMSig sig -> IMSig (Map.map (substvar (ty, var)) sig)
    IMDot ty' field -> IMDot (substvar (ty, var) ty') field
    -- TODO
    IMNamed id nme params instances -> 
      case var of  
        Left str -> 
          if str == nme then term else noShadow
        Right _ -> noShadow
      where
        noShadow = IMNamed id nme
                    (map (substvar (ty, var)) params)
                    (map (map (substvar (ty, var))) instances)

    IMEffect effs rettype -> 
      IMEffect (Set.map (substeff (ty, var)) effs) (substvar (ty, var) rettype)
      where
        substeff _ IEffIO = IEffIO
        substeff s (ICustomEff id tys) = ICustomEff id (map (substvar s) tys)

    IMVector ty' -> IMVector (substvar (ty, var) ty')

    ITypeN _ -> term
    IMPrim _ -> term

-- Throw an error if a variable (string) is contained in a substitution
checkSubst :: String -> String -> LRSubst -> TypeM ()
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
occurs :: Either String Int -> InfType -> Bool
occurs _ (IMVar _) = False
occurs v t = occurs' v t

-- OccursCheck': Subtly different from occurs, this algorithm is recursive:
-- occurs' is true for variable v and type t if v = t or occurs' is
-- true for v and all subterms in t
occurs' :: Either String Int -> InfType -> Bool
occurs' v1 (IMVar v2) = v1 == v2
occurs' v (IMSig sig) = Map.foldr (\ty b -> b || occurs' v ty) False sig
occurs' v (IMArr t1 t2) = occurs' v t1 || occurs' v t2
occurs' v (IMDep t1 str t2) = -- remember: dependent type binding can shadow!
  case v of
    Left str' ->
      if str' == str then
        occurs' v t1
      else
        noShadow
    Right _ -> noShadow
  where noShadow =  occurs' v t1 || occurs' v t2
occurs' v (IMImplDep t1 str t2) = -- remember: dependent type binding can shadow!
  case v of
    Left str' ->
      if str' == str then
        occurs' v t1
      else
        noShadow
    Right _ -> noShadow
  where 
    noShadow = occurs' v t1 || occurs' v t2
occurs' v (IMDot ty _) = occurs' v ty
occurs' v (IMNamed _ name ps instances) = 
  case v of 
    Left str ->
      if str == name then False else noShadow
    Right _ -> noShadow
  where
    noShadow =
      (foldr (||) False (map (occurs' v) ps)) 
      ||
      (foldr (\l b -> foldr (||) False l || b) False (map (map (occurs' v)) instances))
occurs' v (IMEffect effects rettype) = 
  occurs' v rettype
  ||
  Set.foldr (||) False (Set.map (effOccurs v) effects) 
  where
    effOccurs v IEffIO = False
    effOccurs v (ICustomEff id tys) = (foldr (||) False (map (occurs' v) tys))
occurs' v (IMVector ty) = occurs' v ty

occurs' _ (ITypeN _) = False
occurs' _ (IMPrim _) = False
  

-- MISC TYPE UTILS
-- depType: given a value
-- + if it is a type return that type
-- + if it is a module, return the (dependent) type of that module
-- Intended to be used so arguments to 'dependent' functions can be converted
-- into types, and then substituted in to make sure it all works!
-- depType :: TIntermediate -> TypeM (InfType)
-- depType (TValue (TypeN t)) = pure t
-- depType (TValue (Module m)) = do 
--   lst <- mapM (\(s, v) -> do
--                    t' <- depType (TValue v)
--                    pure (Just (s, t'))
--                    `catchError` (\_ -> pure Nothing)) (Map.toList m)
--   --lst :: [(Maybe (String, ModulusType))]
--   let lst' = foldr (\v tl -> case v of
--                        Just x -> x : tl
--                        Nothing -> tl) [] lst
--   pure (Signature (Map.fromList lst'))

-- depType v = throwError ("cannot get as dep-type: " <> show v)


-- Second Phase: post-check
-- The coalesce function takes a Typed Intermediate whose type is an InfType,
-- and replaces it with a typed intermediate whose type is a ModulusType 
coalesce :: TIntermediate InfType -> TIntermediate ModulusType
coalesce term = case term of 
  (TValue v)        -> TValue v
  (TSymbol s)       -> TSymbol s
  (TApply l r)      -> TApply (coalesce l) (coalesce r) 
  (TImplApply l r)  -> TImplApply (coalesce l) (coalesce r)
  (TModule defs)    -> TModule (map coalesceDef defs)
  (TSignature defs) -> TSignature (map coalesceDef defs)
  (TLambda args body rettype) -> TLambda (map coalesceArg args) (coalesce body) (fmap toMls rettype)
  (TIF cond e1 e2)  -> TIF (coalesce cond) (coalesce e1) (coalesce e2)
  (TAccess e str)   -> TAccess (coalesce e) str 


  where 
    coalesceArg :: (TArg InfType, Bool) -> (TArg ModulusType, Bool)
    coalesceArg (BoundArg str ty, bl) = (BoundArg str (toMls ty), bl)
    coalesceArg (ValArg str ty, bl) = (ValArg str (toMls ty), bl)
        -- TODO: change to exception monad!

coalesceDef :: TDefinition InfType -> TDefinition ModulusType
coalesceDef (TVariantDef name args id defs ty) = 
  TVariantDef name args id (map (\(nme, id, ts) -> (name, id, (map toMls ts))) defs) (toMls ty)
coalesceDef (TEffectDef name args id defs) = 
  TEffectDef name args id (map (\(nme, id, ts) -> (name, id, (map toMls ts))) defs)  
coalesceDef (TSingleDef name e ty) = 
  TSingleDef name (coalesce e) (fmap toMls ty)
coalesceDef (TOpenDef e ty) = TOpenDef (coalesce e) (fmap toMls ty)
 

coalesceTop :: TIntTop InfType -> TIntTop ModulusType 
coalesceTop (TExpr term) = TExpr (coalesce term)
coalesceTop (TDefinition def) = TDefinition (coalesceDef def)
  
