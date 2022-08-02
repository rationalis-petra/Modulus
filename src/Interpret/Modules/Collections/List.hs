module Interpret.Modules.Collections.List (listModule) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map

import qualified Data.Map as Map
import Data
import Interpret.Transform
import Interpret.Modules.BuildModule

-- mlsCons = CustomCtor 2 [] consCtor consDtor Undef
--   where
--     consCtor :: [Expr] -> EvalM Expr
--     consCtor [e1, e2] = 
--       case e1 of 
--         Coll (List lst) -> pure $ Coll (List (e2 : lst))
--         (CustomCtor 0 [] c _ _) -> do
--           out <- c [] -- (\x -> Just [x]) <$> (c [])
--           case out of 
--             Coll (List lst) -> pure $ Coll (List (e2 : lst))
--             _ -> lift $ throwError "cannot provide non-list to tail of Cons: "
--         x -> lift $ throwError ("cannot provide non-list to tail of Cons: " <> show x)
--     consCtor _ = lift $ throwError "cons ctor requires only 2 args"

--     consDtor :: Expr -> EvalM (Maybe [Expr])
--     consDtor val = 
--       case val of
--         Coll (List (x:xs)) -> pure $ Just [x, Coll (List xs)]
--         (CustomCtor 0 [] c _ _) -> (\x -> Just [x]) <$> (c [])
--         _ -> pure Nothing 

-- mlsNil = CustomCtor 0 [] nilCtor nilDtor Undef
--   where
--     nilCtor :: [Expr] -> EvalM Expr
--     nilCtor [] = pure $ Coll (List [])
--     nilCtor _ = lift $ throwError "too many args to nil not have a ctor"

--     nilDtor :: Expr -> EvalM (Maybe [Expr])
--     nilDtor val = 
--       case val of
--         Coll (List []) -> pure $ Just []
--         Coll _ -> pure Nothing 

listModuleSource = "\
\ (module \
\  (variant List [a] (Cons a (List a)) Nil) \
\   \ 
\  (defsyntax lst [ast] \
\    (let (to-list (λ [ast] \
\      (match ast      \
\        (Cons (Node x) xs → Cons x (to-list xs)) \
\        (Cons (Atom x) xs → Cons x (to-list xs)) \
\        (Nil → Nil))))  \
\      (match ast        \
\        (Node xs → Atom (to-list xs))  \
\        (Atom a → Atom (Cons a Nil)))))  \

\   (defn flatten [l]\
\     (match l \
\       (Cons x xs → (x ⋅ flatten xs))\
\       (Nil → Nil)))\
 
\   (defn append [l1 l2] \
\     (match l1      \
\       (Cons x xs → Cons x (append xs l2))\
\       (Nil → l2))) \
\   (def `⋅` append) \

\   (defn map [f l] \
\     (match l      \
\       (Cons hd tl → Cons (f hd) (map f tl))\
\       (Nil → Nil))) \

\   (defn app [l1 l2]\
\     (match l1\
\       (Cons f fs → (f xs ⋅ app fs l2))\
\       (Nil → l2)))\
\   (def `<*>` app) \
 
\   (defn pure [f] \
\     (Cons f Nil)) \ 

\   (defn bind [l1 f]\
\     (flatten (map f l1))) \
\   (def `>>=` bind))"


listModule :: EvalM Expr
listModule = pure (Module Map.empty)
-- listModule = buildModule
--                Map.empty
--                listModuleSource
