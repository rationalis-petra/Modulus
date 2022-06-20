module Test where

import Typecheck.FOmega

import Data(PrimType(..))
import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.State (State, StateT, runStateT, lift)


typeTest expr ty = do
  ty' <- inferExpr expr emptyEnv
  eq <- typeEq ty ty'
  if eq then pure ()
  else throwError ("expecting same types, got " <> show ty <> " and " <> show ty')

runTests :: [InferMonad ()] -> IO ()
runTests (x : xs) = 
  -- let final = runStateT x initialState in
  let e = runStateT x initialState
  in 
  case runExcept e of
    Left err -> (print err) >> runTests xs
    Right (_, _) -> runTests xs
    -- Right (False, _) -> (print "test fail") >> runTests xs
runTests [] = pure ()

tests = [
  -- λ x : int → x :: int → int
  typeTest (LamE "x" (PrimT IntT) (VarE "x"))
    (ArrT (PrimT IntT) (PrimT IntT)),


  -- Λ a : ω. λ x : a. x :: ∀ a:ω. a → a
  typeTest (GenE "a" BaseK (LamE "x" (VarT "a") (VarE "x")))
    (AllT "a" BaseK (ArrT (VarT "a") (VarT "a"))),

  -- Λ a : ω → ω. λ x : a int. x :: ∀ a:ω→ω. a int → a int
  typeTest (GenE "a" (ArrK BaseK BaseK) (LamE "x" (AppT (VarT "a") (PrimT IntT)) (VarE "x")))
    (AllT "a" (ArrK BaseK BaseK) (ArrT (AppT (VarT "a") (PrimT IntT)) (AppT (VarT "a") (PrimT IntT)))),

  
  -- λ x:(∃ f:ω→ω. ∀a. a → f a). λ z:int. .
  --    let pack (b, r) = x in (pack (b int) r int z : (∃c:ω. c))
  -- ::
  -- (∃ f:ω→ω. {t=f, pure=∀a.a → f a) → int → (∃ c:ω.c)
  typeTest (LamE "x" (ExistsT "f" (ArrK BaseK BaseK)
                      (RecT [("t", VarT "f"),
                             ("pure", AllT "a" BaseK (ArrT (VarT "a") (AppT (VarT "f") (VarT "a"))))]))
             (Unpack (VarE "x") "b" "m"
              (LamE "z" (PrimT IntT)
                (PackE (AppT (VarT "b") (PrimT IntT)) 
                  (AppE (Inst (AccessE (VarE "m") "pure") (PrimT IntT)) (VarE "z"))
                  (ExistsT "c" BaseK (VarT "c"))))))
    (ArrT
      (ExistsT "f" (ArrK BaseK BaseK)
       (RecT [("t", VarT "f"),
              ("pure", AllT "a" BaseK (ArrT (VarT "a") (AppT (VarT "f") (VarT "a"))))]))
      (ArrT
       (PrimT IntT)
       (ExistsT "c" BaseK (VarT "c"))))


  -- todo: composable functions on types
  -- .e.g
  -- map lst (λ x. x + 3)
  -- add3 :: ∃ f:ω→ω. ({pure : ∀ a. a→f a, map: ∀ a,b. (a→b)→(f a)→(f b)} → 
  -- add3 = 

  -- λ x: int. add3 List (List.pure n) 

  
  ]



runTypeTests = runTests tests


