module Interpret.Structures.System where

import qualified Data.Map as Map

import Data
import Data.Text(pack, unpack)
import Interpret.Transform

mlsGetLine :: [Normal] -> IO (EvalM Normal)
mlsGetLine [x] = do
  line <- getLine
  pure $ pure $ PrimVal $ String (pack line)

mlsPutLine :: [Normal] -> IO (EvalM Normal)
mlsPutLine [(PrimVal (String str))] = do
  putStrLn (unpack str)
  pure $ pure $ PrimVal Unit

systemStructure :: [(String, Normal)]
systemStructure = [
  ("getLine", IOAction 0 1 mlsGetLine []),
  ("putLine", IOAction 1 1 mlsPutLine [])
  ]
