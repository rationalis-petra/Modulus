{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.System.Console (consoleStructure, consoleSignature) where

import qualified Data.Map as Map
import Control.Monad.State (MonadState)
import Control.Monad.Except (MonadError)
import Control.Monad.Reader (MonadReader)

import System.IO
import Syntax.Normal
import Interpret.Eval (liftFun)
import Interpret.Environment (Environment)
  
import Data.Text(pack, unpack)

mlsGetLine :: (Applicative m) => Normal m
mlsGetLine = CollVal (IOAction (IOThread m) getType)
  where m :: (Applicative m) => IO (IEThread m)
        m = Pure . pure . PrimVal . String . pack  <$> getLine

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

consoleSignature :: Normal m
consoleSignature = NormSig $ [("get-line", getType), ("put-line", putType)]

consoleStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
consoleStructure = NormSct (toEmpty
                  [ ("get-line", mlsGetLine) 
                  , ("put-line", mlsPutLine)
                  ]) consoleSignature
