{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.System (systemStructure, systemSignature) where

import qualified Data.Map as Map
import Control.Monad.State (MonadState)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (MonadReader)

import System.IO
import Syntax.Normal
import Interpret.Eval (liftFun)
  
import Data.Text(pack, unpack)

mlsGetLine :: (Applicative m) => Normal m
mlsGetLine = CollVal (IOAction (IOThread m) getType)
  where m :: (Applicative m) => IO (IEThread m)
        m = do
          line <- getLine
          pure . Pure . pure . PrimVal $ String (pack line)

mlsPutLine :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsPutLine = liftFun f putType
  where f :: (Applicative m) => Normal m -> m (Normal m)
        f (PrimVal (String str)) = pure $ CollVal $ IOAction
                                    (IOThread $ do
                                        putStrLn (unpack str)
                                        hFlush stdout
                                        pure . Pure . pure $ PrimVal Unit)
                                    (CollTy (IOMonadTy (PrimType UnitT)))

putType :: Normal m
putType = NormArr (PrimType StringT) (CollTy (IOMonadTy (PrimType UnitT)))

getType :: Normal m
getType = CollTy (IOMonadTy (PrimType StringT))

systemSignature :: Normal m
systemSignature = NormSig $ [("get-line", getType), ("put-line", putType)]

systemStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
systemStructure = NormSct (toEmpty
                  [ ("get-line", mlsGetLine) 
                  , ("put-line", mlsPutLine)
                  ]) systemSignature
