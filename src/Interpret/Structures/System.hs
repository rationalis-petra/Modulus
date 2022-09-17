module Interpret.Structures.System (systemStructure, systemSignature) where

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

putType = NormArr  (PrimType StringT) (NormEffect [IOEffect] (PrimType UnitT))
getType = NormArr (PrimType UnitT) (NormEffect [IOEffect] (PrimType StringT))

systemSignature :: Normal  
systemSignature = NormSig $ [("get-line", getType), ("put-line", putType)]

systemStructure :: [(String, Normal)]
systemStructure = [
  ("get-line", IOAction 0 1 mlsGetLine [] getType),
  ("put-line", IOAction 1 1 mlsPutLine [] putType)
  ]
