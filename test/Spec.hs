import Parse
import Test

main :: IO ()
main = do
  runParseSuite
  runTypeTests
  putStrLn "tests complete"
