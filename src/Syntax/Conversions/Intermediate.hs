module Syntax.Conversions.Intermediate where

import Prelude hiding (lookup)
import Data.Text (unpack)

import Control.Monad.Except (Except, runExcept, throwError) 
import qualified Data.Set as Set
import qualified Interpret.Environment as Env
import Data (AST(..),
             Environment,
             Special(..),
             Normal(Symbol, Special, Keyword, NormIVal, NormCoDtor, PrimVal),
             PrimVal(String),
             Neutral)

import Syntax.Intermediate

newtype GlobCtx m = GlobCtx (Environment m, (Set.Set String))

  


lookup s (GlobCtx (ctx, shadowed)) = 
  if Set.member s shadowed then
    Nothing
  else
    -- TODO: this was lookupGlbl previously... why??
    -- probably: we could only get values if it was 
    fst <$> Env.lookupGlblS s ctx

shadow s (GlobCtx (ctx, shadowed)) = 
  GlobCtx (ctx, Set.insert s shadowed)

toIntermediate :: AST m -> Environment m -> Either String (Intermediate m)
toIntermediate val ctx =
  runExcept (toIntermediateM val (GlobCtx (ctx, Set.empty)))

toIntermediateTop (Cons (e : es)) ctx = do
  val <- toIntermediateM e ctx
  case val of  
    (IValue (Special Lambda)) -> mkLambda es ctx

toIntermediateM :: AST m -> GlobCtx m -> Except String (Intermediate m)
toIntermediateM (Atom (Symbol s)) ctx =
  case lookup s ctx of 
    Just x -> pure (IValue x)
    Nothing -> pure (ISymbol s)
toIntermediateM (Atom e) _ = pure (IValue e)
toIntermediateM (Cons (e : es)) ctx = do
  val <- toIntermediateM e ctx
  case val of  
    (IValue (Special Def)) -> mkDef es Nothing ctx >>= (pure . IDefinition)
    (IValue (Special Induct)) -> mkInduct IInductDef es ctx >>= (pure . IDefinition)
    (IValue (Special Coinduct)) -> mkInduct ICoinductDef es ctx >>= (pure . IDefinition)
    (IValue (Special Do)) -> mkDo es ctx
    (IValue (Special Lambda)) -> mkLambda es ctx
    (IValue (Special Mac)) -> mkMacro es ctx
    (IValue (Special Let)) -> mkLet es ctx
    (IValue (Special If)) -> mkIf es ctx
    (IValue (Special Access)) -> mkAccess es ctx
    (IValue (Special MkStructure)) -> mkModule es ctx
    (IValue (Special MkSig)) -> mkSig es ctx
    (IValue (Special MkProd)) -> mkProd es ctx
    (IValue (Special Open)) -> (mkOpen es ctx) >>= (pure . IDefinition)
    (IValue (Special LetOpen)) -> (mkLetOpen es ctx)
    (IValue (Special MkQuote)) -> case es of
      [x] -> pure $ IQuote x
      _   -> throwError "Quote expects a single argument"

    (IValue (Special MkMatch)) -> mkMatch es ctx
    (IValue (Special MkCoMatch)) -> mkCoMatch es ctx
    (IValue (Special Annotate)) -> mkAnnotate es ctx
    (IValue (Special ForeignAdapter)) -> mkAdapter es ctx
    _ -> do
      args <- mapM (\v -> toIntermediateM v ctx) es
      let mkApply v [] = v
          mkApply v ((IApply (IValue (Keyword "implicit")) x) : xs) = (mkApply (IImplApply v x) xs)
          mkApply v (x : xs) = (mkApply (IApply v x) xs)
      return (mkApply val args)

mkIf :: [AST m] -> GlobCtx m -> Except String (Intermediate m)   
mkIf [cond, e1, e2] ctx = do
  cond' <- toIntermediateM cond ctx
  e1' <- toIntermediateM e1 ctx
  e2' <- toIntermediateM e2 ctx
  pure $ IIF cond' e1' e2'
mkIf ast _ = throwError ("bad syntax in if: " ++ show ast)

mkLambda :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkLambda [syms, body] ctx = do
  symList <- getAnnSymList syms ctx
  let new_ctx = fold (shadowbnd) symList ctx
      fold f [] v = v
      fold f (x:xs) v = f x (fold f xs v)
      shadowbnd (Annotation s _) = shadow s
      shadowbnd (Sym s) = shadow s
  body <- toIntermediateM body new_ctx
  pure $ ILambda (map (\x -> (x, False)) symList) body
mkLambda [Cons (Atom (Keyword "implicit") : isyms), syms, body] ctx = do
  implList <- getAnnSymList (Cons isyms) ctx
  symList <- getAnnSymList syms ctx
  let new_ctx' = fold shadowbnd implList ctx
      new_ctx = fold shadowbnd symList new_ctx' 
      fold f [] v = v
      fold f (x:xs) v = f x (fold f xs v)
      shadowbnd (Annotation s _) = shadow s
      shadowbnd (Sym s) = shadow s
  body <- toIntermediateM body new_ctx
  pure $ ILambda (map (\x -> (x, True)) implList <> map (\x -> (x, False)) symList) body
mkLambda ast _ = throwError ("bad syntax in lambda: " ++ show ast)

mkProd :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkProd [arg, body] ctx = 
  let (impl, arg') = case arg of
        Cons [Atom (Keyword "implicit"), arg'] -> (True, arg')
        _ -> (False, arg)
  in do
    (arg'', var) <- case arg' of
          Cons [hd, Atom (Symbol s), ty] -> do
            val <- toIntermediateM hd ctx
            case val of 
              -- TODO: this is dodgy: make annotation a possible return value of toIntermediateM
              (IValue (Special Annotate)) -> do
                ty' <- toIntermediateM ty ctx
                pure (Annotation s ty', Just s)
              _ -> do
                ty' <- toIntermediateM (Cons [hd, Atom (Symbol s), ty]) ctx
                pure (IWildCardArg ty', Nothing)
          ty -> do
            ty' <- toIntermediateM ty ctx
            pure (IWildCardArg ty', Nothing)
    case var of    
      Just v -> IProd (arg'', impl) <$> toIntermediateM body (shadow v ctx) 
      Nothing -> IProd (arg'', impl) <$> toIntermediateM body ctx 
mkProd ast _ = throwError ("bad syntax in product (→): " ++ show ast)


mkMacro :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkMacro [syms, body] ctx = do
  symList <- getAnnSymList syms ctx
  let new_ctx = fold (shadowbnd) symList ctx
      fold f [] v = v
      fold f (x:xs) v = f x (fold f xs v)
      shadowbnd (Annotation s _) = shadow s
      shadowbnd (Sym s) = shadow s
  body <- toIntermediateM body new_ctx
  pure $ IMacro symList body
mkMacro ast _ = throwError ("bad syntax in syntax: " ++ show ast)
  

mkLet :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkLet lst ctx = do
  (binds, body) <- splitLast lst  
  bindList <- getBindList (Cons binds) ctx
  let new_ctx = fold shadow (map (\(x, _) -> x) bindList) ctx
      fold f [] v = v
      fold f (x:xs) v = f x (fold f xs v)
  body <- toIntermediateM body new_ctx
  pure $ ILet bindList body
  where
    splitLast :: [a] -> Except String ([a], a)
    splitLast [] = throwError "let clause too short"
    splitLast [x] = pure ([], x)
    splitLast (x : xs) =
      splitLast xs >>= (\(l, last) -> pure (x : l, last))

mkDef :: [AST m] -> Maybe (String, Intermediate m) -> GlobCtx m -> Except String (IDefinition m)
mkDef [(Atom (Symbol s)), body] ann ctx = 
  let new_ctx = shadow s ctx in do
    body' <- toIntermediateM body new_ctx
    case ann of 
      Just (s', term) -> do
        if s' == s then
          pure $ (ISingleDef s body' (Just term))
        else
          throwError "annotation must match subsequent definition"
      Nothing ->
        pure $ (ISingleDef s body' Nothing)
mkDef ast _ _ = throwError ("bad syntax in def: " ++ show ast)

mkModule :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkModule lst ctx = do
  defs <- foldDefs lst Nothing ctx 
  return $ IStructure defs
  where
    foldDefs :: [AST m] -> Maybe (String, Intermediate m) -> GlobCtx m ->  Except String [IDefinition m]
    foldDefs [] _ _ = pure []
    foldDefs ((Cons (op : body)) : tl) ann ctx = do
      mdef <- toIntermediateM op ctx
      case mdef of 
        -- TODO: shadow all variables...
        (IValue (Special Annotate)) -> do
          case (body, ann) of
            ([Atom (Symbol s), term], Nothing) -> do
              term' <- toIntermediateM term ctx
              foldDefs tl (Just (s, term')) ctx
            (_, Just _) -> throwError "cannot have two sequential annotations"
            (_, _) -> throwError "malformed module annotation"
        (IValue (Special Def)) -> do
          def <- mkDef body ann ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl Nothing (foldr shadow ctx syms)
          pure $ def : tl'
        (IValue (Special Induct)) -> do
          def <- mkInduct IInductDef body ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl Nothing (foldr shadow ctx syms)
          pure $ def : tl'
        (IValue (Special Coinduct)) -> do
          def <- mkInduct ICoinductDef body ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl Nothing (foldr shadow ctx syms)
          pure $ def : tl'
        (IValue (Special Open)) -> do
          def <- mkOpen body ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl Nothing (foldr shadow ctx syms)
          pure $ def : tl'
        _ -> throwError "Modules should contain only definition terms"
    foldDefs v _ _ = throwError ("bad term in module definition: " ++ show v)

mkSig :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkSig lst ctx = do
  defs <- foldDefs lst ctx
  return $ ISignature defs
  where
    foldDefs :: [AST m] -> GlobCtx m -> Except String [IDefinition m]
    foldDefs [] _ = pure []
    foldDefs ((Cons (op : body)) : tl) ctx = do
      mdef <- toIntermediateM op ctx
      case mdef of 
        -- TODO: shadow all variables...
        (IValue (Special Annotate)) -> do
          def <- mkDef body Nothing ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl (foldr shadow ctx syms)
          pure $ def : tl'
        (IValue (Special Def)) -> do
          def <- mkDef body Nothing ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl (foldr shadow ctx syms)
          pure $ def : tl'
        (IValue (Special Induct)) -> do
          def <- mkInduct IInductDef body ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl (foldr shadow ctx syms)
          pure $ def : tl'
        (IValue (Special Coinduct)) -> do
          def <- mkInduct ICoinductDef body ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl (foldr shadow ctx syms)
          pure $ def : tl'
        (IValue (Special Open)) -> do
          def <- mkOpen body ctx
          let syms = getDefSyms def 
          tl' <- foldDefs tl (foldr shadow ctx syms)
          pure $ def : tl'
        _ -> throwError "Signatures should contain only definition terms"
    foldDefs v _ = throwError ("bad term in signature definition: " ++ show v)


mkInduct :: (String -> [IArg m] -> Intermediate m -> [(String, Intermediate m)] -> IDefinition m)
         -> [AST m] -> GlobCtx m ->  Except String (IDefinition m)
mkInduct constructor (def : tl) ctx = do
  (sym, params, ty) <- extractDef def ctx
  alternatives <- mkAlternatives tl (shadow sym ctx)
  pure $ constructor sym params ty alternatives
  where
    extractDef :: AST m -> GlobCtx m -> Except String (String, [IArg m], Intermediate m)
    extractDef (Cons [a, Cons [Atom (Symbol s), params], ty]) ctx = do
      a' <- toIntermediateM a ctx
      case a' of 
        (IValue (Special Annotate)) -> do
          params' <- getAnnSymList params ctx
          ty' <- toIntermediateM ty ctx
          pure (s, params', ty')
        _ -> throwError ("Poorly formed header in co/inductive definition: " <> show a')
    extractDef (Cons [a, Atom (Symbol s), ty]) ctx = do
      a' <- toIntermediateM a ctx
      case a' of 
        (IValue (Special Annotate)) -> do
          ty' <- toIntermediateM ty ctx
          pure (s, [], ty')
        _ -> throwError ("Poorly formed header in co/inductive definition expected annotate, got: "
                         <> show a')
    extractDef def _ = throwError ("Poorly formed inductive type head: " <> show def)

    
    mkAlternatives :: [AST m] -> GlobCtx m -> Except String [(String, Intermediate m)] 
    mkAlternatives (hd : tl) ctx = do
      bot <- mkAlternatives tl ctx
      top <- mkAlternative hd ctx
      pure (top : bot)
    mkAlternatives [] ctx = pure []

    mkAlternative :: AST m -> GlobCtx m -> Except String (String, Intermediate m) 
    mkAlternative (Cons [a, Atom (Symbol s), altTy]) ctx = do
      a' <- toIntermediateM a ctx
      case a' of 
        (IValue (Special Annotate)) -> do
          altTy' <- toIntermediateM altTy ctx
          pure (s, altTy')
        _ -> throwError ("Poorly formed co/inductive alternative: " <> show a) 
    mkAlternative a _ = throwError ("Poorly formed co/inductive type alternative: " <> show a)


mkInduct _ _ _ = throwError "ill-formed inductive or coinductive definition"


mkMatch :: [AST m] -> GlobCtx m -> Except String (Intermediate m)  
mkMatch (expr : patterns) ctx = do
  body <- toIntermediateM expr ctx
  patterns <- mkPatterns patterns ctx
  pure $ IMatch body patterns
  where 
    mkPatterns :: [AST m] -> GlobCtx m -> Except String [(IPattern m, Intermediate m)]
    mkPatterns [] _ = pure []
    mkPatterns (Cons [Atom ((Symbol "→")), pat, expr] : xs) ctx = do
      bdy <- toIntermediateM expr ctx
      pat <- mkPattern pat ctx
      tl <- mkPatterns xs ctx
      return $ (pat, bdy) : tl
    mkPatterns x _ = throwError ("ill-formed pattern match " <> show x)

    mkPattern :: AST m -> GlobCtx m -> Except String (IPattern m) 
    mkPattern (Cons (hd : tl)) ctx = do
      val <- toIntermediateM hd ctx 
      patterns <- mapM (\v -> mkPattern v ctx) tl
      pure $ ICheckPattern val patterns

    mkPattern (Atom (Symbol s)) ctx =
      case s of 
        "_" -> pure $ IWildCard
        _ -> case lookup s ctx of
           Just (NormIVal name id1 id2 strip [] ty) ->
             pure $ ICheckPattern (IValue (NormIVal name id1 id2 strip [] ty)) []
           _ -> pure $ ISingPattern s
mkMatch _ _ = throwError "ill-formed pattern-match"

  
mkCoMatch :: [AST m] -> GlobCtx m -> Except String (Intermediate m)  
mkCoMatch (patterns) ctx = do
  patterns <- mkPatterns patterns ctx
  pure $ ICoMatch patterns
  where 
    mkPatterns :: [AST m] -> GlobCtx m -> Except String [(ICoPattern m, Intermediate m)]
    mkPatterns [] _ = pure []
    mkPatterns (Cons [Atom ((Symbol "→")), pat, expr] : xs) ctx = do
      bdy <- toIntermediateM expr ctx
      pat <- mkPattern pat ctx
      tl <- mkPatterns xs ctx
      return $ (pat, bdy) : tl
    mkPatterns x _ = throwError ("ill-formed copattern match " <> show x)

    mkPattern :: AST m -> GlobCtx m -> Except String (ICoPattern m) 
    mkPattern (Cons (hd : tl)) ctx = do
      val <- toIntermediateM hd ctx 
      patterns <- mapM (\v -> mkPattern v ctx) tl
      pure $ ICoCheckPattern val patterns

    mkPattern (Atom (Symbol s)) ctx =
      case s of 
        "_" -> pure $ ICoWildCard
        _ -> case lookup s ctx of
           Just (NormCoDtor name id1 id2 len strip [] ty) ->
             pure $ ICoCheckPattern (IValue (NormCoDtor name id1 id2 len strip [] ty)) []
           _ -> pure $ ICoSingPattern s
  

mkOpen :: [AST m] -> GlobCtx m -> Except String (IDefinition m)
mkOpen [v] ctx = do
  (toIntermediateM v ctx) >>= (\x-> pure $ IOpenDef x)
mkOpen x _ =
      throwError ("ill-formed open clause : " <> show x)

mkLetOpen :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkLetOpen [a1, a2] ctx = do
  mods <- getModules a1
  body <- toIntermediateM a2 ctx
  pure $ ILetOpen mods body
  where
    getModules (Atom _) = do
      mod <- toIntermediateM a1 ctx
      pure [mod]
    getModules (Cons lst) = do
      mods <- mapM (\x -> toIntermediateM x ctx) lst 
      pure mods

mkLetOpen x _ =
      throwError ("ill-formed let-open clause : " <> show x)


mkAccess :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkAccess [hd, (Atom (Symbol s))] globctx = do
  hd' <- toIntermediateM hd globctx
  pure $ IAccess hd' s
mkAccess args _ = throwError ("malformed access: " <> show args)

-- TODO: make do a macro!
mkDo :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkDo es globctx = do
  -- TODO: applicative do (see haskell) 
  term <- foldDo es globctx 
  pure $ term
  where
    foldDo :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
    foldDo [] _ = throwError ("empty do")
    foldDo [x] ctx = toIntermediateM x ctx
    foldDo (x:xs) ctx = case x of 
      -- TODO: replace >> and >>= with their actual implicit versions!
      Cons [Atom (Symbol "←"), Atom (Symbol s), expr] -> do
        rest <- foldDo xs ctx
        expr' <- toIntermediateM expr ctx
        pure $ IApply (IApply (ISymbol ">>=") expr') (ILambda [(Sym s, False)] rest)
      expr -> do
        expr' <- toIntermediateM expr ctx
        rest <- foldDo xs ctx
        pure $ IApply (IApply (ISymbol ">>") expr') rest


mkAnnotate :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkAnnotate [(Atom (Symbol str)), term] ctx  = do
  term' <- toIntermediateM term ctx
  pure (IAnnotation str term')
mkAnnotate args _ = throwError ("malformed annotate: " <> show args)

mkAdapter :: [AST m] -> GlobCtx m -> Except String (Intermediate m)
mkAdapter ((Atom (Symbol lang)) : (Atom (Symbol lib)) : annotations) ctx = do
  annotations' <- mapM (flip mkForeignAnnotate ctx) annotations
  pure $ IAdaptForeign lang lib annotations'
  where
    mkForeignAnnotate :: AST m -> GlobCtx m -> Except String (String, String, Intermediate m)
    mkForeignAnnotate (Cons [ Atom (Symbol ":")
                            , Cons [Atom (Symbol sym), Atom (PrimVal (String fsym))]
                            , term]) ctx = do
      term' <- toIntermediateM term ctx
      pure (sym, unpack fsym, term')
    mkForeignAnnotate args _ = throwError ("malformed foreign annotate: " <> show args)
mkAdapter args _ = throwError ("malformed foreign-adapter: " <> show args)


getAnnSymList :: AST m -> GlobCtx m -> Except String [IArg m]
getAnnSymList (Cons l) ctx = getSymListR l
  where
    --getSymListR :: [AST m] -> Except String [IArg m]
    getSymListR [] = pure [] 
    getSymListR (Atom (Symbol s) : syms) = fmap (Sym s :) (getSymListR syms)
    getSymListR (Cons [Atom (Special Annotate), Atom (Symbol s), x] : syms) = do
      tl <- toIntermediateM x ctx
      fmap (Annotation s tl :) (getSymListR syms)
    getSymListR (Cons [Atom (Symbol a), Atom (Symbol s), x] : syms) = do
      case lookup a ctx of 
        Just (Special Annotate) -> do
          tl <- toIntermediateM x ctx
          fmap (Annotation s tl :) (getSymListR syms)
        _ -> throwError ("malformed argument binding: " <> show x)
    getSymListR (x:xs) = throwError ("malformed argument binding: " <> show x)
getAnnSymList _ _ = throwError "expected symbol-list: encountered atom"
  

getSymList :: AST m -> Except String [String]
getSymList (Cons l) = getSymListR l
  where
  getSymListR :: [AST m] -> Except String [String]
  getSymListR [] = pure [] 
  getSymListR (Atom (Symbol s) : syms) = fmap ((:) s) (getSymListR syms)
  getSymListR _ = throwError "non-symbol encountered in sym-list!"
getSymList _ = throwError "expected symbol-list: encountered atom"

getBindList :: AST m -> GlobCtx m -> Except String [(String, Intermediate m)]
getBindList (Cons (Cons binding : tl)) ctx = do
  case binding of 
    [s, val] -> do
      sym <- getSym s
      val <- toIntermediateM val ctx
      rest <- getBindList (Cons tl) ctx
      pure $ (sym , val) : rest
    [s, args, body] -> do
      sym <- getSym s
      lam <- mkLambda [args, body] ctx
      rest <- getBindList (Cons tl) ctx
      pure $ (sym , lam) : rest
    [s, impl, args, body] -> do
      sym <- getSym s
      lam <- mkLambda [impl, args, body] ctx
      rest <- getBindList (Cons tl) ctx
      pure $ (sym , lam) : rest
  where
    getSym :: AST m -> Except String String
    getSym (Atom (Symbol s)) = pure s
    getSym v = throwError ("non-symbol encountered in sym-list: " <> show v)
getBindList (Cons []) ctx = pure []
getBindList _ _ = throwError "expected bind-list: encountered atom"


spltLast :: [AST m] -> Except String ([String], AST m)
spltLast [] = throwError "variant expects alternative-list"
spltLast [x] = pure ([], x)
spltLast ((Atom (Symbol s)) : xs) = do
  (lst, end) <- spltLast xs
  pure ((s : lst), end)


getDefSyms :: IDefinition m -> [String]  
getDefSyms (ISingleDef s _ _) = [s]
-- getDefSyms (IInductDef)
-- getDefSyms (IEff)
-- getDefSyms ()
