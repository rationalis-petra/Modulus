module Interpret.Modules.System where

import qualified Data.Map as Map

import Data
import Data.Text(pack, unpack)
import Interpret.Transform

mlsGetLine :: [Expr] -> IO (EvalM Expr)
mlsGetLine [x] = do
  line <- getLine
  pure $ pure $ PrimE $ String (pack line)

mlsPutLine :: [Expr] -> IO (EvalM Expr)
mlsPutLine [(PrimE (String str))] = do
  putStrLn (unpack str)
  pure $ pure $ PrimE Unit

systemModule :: Map.Map String Expr
systemModule = Map.fromList [
  ("getLine", IOAction 0 1 mlsGetLine []),
  ("putLine", IOAction 1 1 mlsPutLine [])
  ]
