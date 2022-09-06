module TypeTest where

import Typecheck.Typecheck2

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
