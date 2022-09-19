module Interpret.Structures.System (systemStructure, systemSignature) where

import qualified Data.Map as Map

import Data
import Interpret.Eval (liftFun)
  
import Data.Text(pack, unpack)
import Interpret.Transform

mlsGetLine :: Normal
mlsGetLine = CollVal (IOAction m getType)
  where m = do
          line <- getLine
          pure $ PrimVal $ String (pack line)

mlsPutLine :: Normal
mlsPutLine = liftFun f putType  
  where f :: Normal -> EvalM Normal
        f (PrimVal (String str)) = pure $ CollVal $ IOAction (do
          putStrLn (unpack str)
          pure $ PrimVal Unit) putType

putType :: Normal
putType = NormArr (PrimType StringT) (CollTy (IOMonadTy (PrimType UnitT)))

getType :: Normal
getType = CollTy (IOMonadTy (PrimType StringT))

systemSignature :: Normal  
systemSignature = NormSig $ [("get-line", getType), ("put-line", putType)]

systemStructure :: [(String, Normal)]
systemStructure = [
  ("get-line", mlsGetLine),
  ("put-line", mlsPutLine)
  ]
