{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Data.String where

import Control.Monad.Reader (MonadReader)
import Control.Monad.State  (MonadState)
import Control.Monad.Except (MonadError, throwError)

import qualified Data.Map as Map
import Data.Text as Text

import Syntax.Normal
import Interpret.Lib.LibUtils
import Syntax.Utils (mkVar)
import Interpret.Eval (liftFun, liftFun2)
import Interpret.EvalM
import Interpret.Environment (Environment)

  

fnConcat :: (MonadError String m) => Normal m -> Normal m -> m (Normal m)  
fnConcat (PrimVal (String s1)) (PrimVal (String s2)) =
  pure $ PrimVal $ String (s1 <> s2)
fnConcat _ _ = throwError "append expects strings as arguments"

  
mlsConcat :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsConcat = liftFun2 fnConcat (NormArr (PrimType StringT)
                               (NormArr (PrimType StringT) (PrimType StringT)))


mlsElement :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsElement = liftFun2 element (NormArr (PrimType StringT)
                               (NormArr (PrimType IntT) (PrimType CharT)))
  where
    element :: MonadError String m => Normal m -> Normal m -> m (Normal m)
    element (PrimVal (String s)) (PrimVal (Int i)) =
      pure $ PrimVal $ Char (index s (fromEnum i))
    element _ _ = throwError "element expects string/idx as arguments"


mlsLength :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
mlsLength = liftFun len (NormArr (PrimType StringT) (PrimType IntT))
  where
    len :: (MonadError String m) => Normal m -> m (Normal m)
    len (PrimVal (String s)) =
      pure $ PrimVal $ Int (toInteger (Text.length s))
    len _ = throwError "length expects string as an argument"


strShow :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
strShow = liftFun sshow (NormArr (PrimType StringT) (PrimType StringT))
  where
    sshow :: (MonadError String m) => Normal m -> m (Normal m)
    sshow (PrimVal (String s)) = pure (PrimVal (String s))
    sshow _ = throwError "length expects string as an argument"

  
strEq :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
strEq = liftFun2 eq (NormArr (PrimType StringT) (NormArr (PrimType StringT) (PrimType BoolT)))
  where
    eq :: (MonadError String m) => Normal m -> Normal m -> m (Normal m)
    eq (PrimVal (String s1)) (PrimVal (String s2)) = pure (PrimVal (Bool (s1 == s2)))
    eq _ _ = throwError "string = expects two strings as arguments"

showableTy :: Normal m
showableTy = NormUniv 0

showable :: Normal m
showable = NormSig 
  [ ("T", NormUniv 0)
  , ("show", NormArr (mkVar "T") (PrimType StringT))
  ]

implShowTy :: Normal m
implShowTy = NormProd "s" Hidden showable 
             (NormArr st (PrimType StringT))
  where st = Neu (NeuDot (NeuVar "s" showable) "T") showable

implShow :: Normal m
implShow =
  NormAbs "s" (NormAbs "x" (Neu (NeuApp (NeuDot (NeuVar "s" showable) "show") (Neu (NeuVar "x" t2) t2)) t2) t1) t0
  where
    t0 = implShowTy
    t1 = tyTail t0
    t2 = tyTail t1
  
stringSignature :: Normal m
stringSignature = NormSig
                  [ ("String",  NormUniv 0)
                  , ("T",       NormUniv 0)
                  , ("Showable", showableTy)
                  , ("append",  (NormArr t (NormArr t t)))
                  , ("⋅",       (NormArr t (NormArr t t)))
                  , ("show",    (NormArr t (PrimType StringT)))
                  , ("!!",      (NormArr t (NormArr (PrimType IntT) (NormArr t t))))
                  , ("=",       (NormArr (PrimType StringT) (NormArr (PrimType StringT) (PrimType BoolT))))
                  , ("index",   (NormArr t (NormArr (PrimType IntT) (NormArr t t))))
                  ]
  where
    t = Neu (NeuVar "T" (NormUniv 0)) (NormUniv 0)

stringStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
stringStructure = NormSct (toEmpty
                  [ ("String", PrimType StringT)
                  , ("T",      PrimType StringT)
                  , ("Showable", showable)
                  , ("append", mlsConcat)
                  , ("⋅",      mlsConcat)
                  , ("show",   strShow)
                  , ("!!",     mlsElement)
                  , ("=",      strEq)
                  , ("index",  mlsElement)
                  ]) stringSignature
