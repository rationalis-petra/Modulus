module Interpret.Lib.System (systemStructure, systemSignature) where

import qualified Data.Map as Map

import System.IO
import Data
import Interpret.Eval (liftFun)
  
import Data.Text(pack, unpack)

mlsGetLine :: Normal
mlsGetLine = CollVal (IOAction m getType)
  where m :: IO (EvalM Normal)
        m = do
          line <- getLine
          pure $ pure $ PrimVal $ String (pack line)

mlsPutLine :: Normal
mlsPutLine = liftFun f putType  
  where f :: Normal -> EvalM Normal
        f (PrimVal (String str)) = pure $ CollVal $ IOAction (do
          putStrLn (unpack str)
          hFlush stdout
          pure $ pure $ PrimVal Unit) (CollTy (IOMonadTy (PrimType UnitT)))

putType :: Normal
putType = NormArr (PrimType StringT) (CollTy (IOMonadTy (PrimType UnitT)))

getType :: Normal
getType = CollTy (IOMonadTy (PrimType StringT))

systemSignature :: Normal  
systemSignature = NormSig $ [("get-line", getType), ("put-line", putType)]

systemStructure :: Normal
systemStructure = NormSct (toEmpty
                  [ ("get-line", mlsGetLine) 
                  , ("put-line", mlsPutLine)
                  ]) systemSignature
