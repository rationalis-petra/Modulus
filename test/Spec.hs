import Parse
import TypeTest

main :: IO ()
main = do
  runParseSuite
  -- runTypeTests
  putStrLn "tests complete"
