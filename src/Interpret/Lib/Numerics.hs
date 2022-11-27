{-# LANGUAGE FlexibleContexts #-}
module Interpret.Lib.Numerics (numStructure, numSignature) where

import qualified Data.Map as Map
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (MonadState)
import Control.Monad.Except (MonadError)

import Data
import Data.Text (pack)
import Interpret.EvalM
import Interpret.Eval (liftFun, liftFun2)

int_t = PrimType IntT
bool_t = PrimType BoolT
float_t = PrimType FloatT

mkVar s = (Neu (NeuVar s (NormUniv 0)) (NormUniv 0))

floatShow :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
floatShow = liftFun newf (NormArr float_t (PrimType StringT))
  where
    newf :: Applicative m => Normal m -> m (Normal m)
    newf (PrimVal (Float f)) = pure (PrimVal (String (pack (show f))))


mkFloatUni :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Float -> Float) -> Normal m
mkFloatUni f = 
  liftFun newf unifloat
  where
    newf :: Applicative m => Normal m -> m (Normal m)
    newf (PrimVal (Float f1)) = pure $ PrimVal $ Float $ f f1


mkFloatOp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Float -> Float -> Float) -> Normal m
mkFloatOp f = 
  liftFun2 newf binfloat
  where
    newf :: Applicative m => Normal m -> Normal m -> m (Normal m)
    newf (PrimVal (Float f1)) (PrimVal (Float f2)) =
      pure $ PrimVal $ Float $ f f1 f2


mkFltCmp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Float -> Float -> Bool) -> Normal m
mkFltCmp f = 
  liftFun2 newf floatCompare
  where
    newf :: Applicative m => Normal m -> Normal m -> m (Normal m)
    newf (PrimVal (Float n1)) (PrimVal (Float n2)) =
      pure $ PrimVal $ Bool $ f n1 n2


intShow :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
intShow = liftFun newf (NormArr int_t (PrimType StringT))
  where
    newf :: Applicative m => Normal m -> m (Normal m)
    newf (PrimVal (Int n1)) = pure (PrimVal (String (pack (show n1))))
  

mkIntUni :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Integer -> Integer) -> Normal m
mkIntUni f = 
  liftFun newf uniint
  where
    newf :: Applicative m => Normal m -> m (Normal m)
    newf (PrimVal (Int n1)) = pure $ PrimVal $ Int $ f n1

  
mkIntOp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Integer -> Integer -> Integer) -> Normal m
mkIntOp f = 
  liftFun2 newf binint
  where
    newf :: Applicative m => Normal m -> Normal m -> m (Normal m)
    newf (PrimVal (Int n1)) (PrimVal (Int n2)) =
      pure $ PrimVal $ Int $ f n1 n2


mkCmpOp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Integer -> Integer -> Bool) -> Normal m
mkCmpOp f = 
  liftFun2 newf intcompare
  where
    newf :: Applicative m => Normal m -> Normal m -> m (Normal m)
    newf (PrimVal (Int n1)) (PrimVal (Int n2)) =
      pure $ PrimVal $ Bool $ f n1 n2


mkBoolOp :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Bool -> Bool -> Bool) -> Normal m
mkBoolOp f = 
  liftFun2 newf binbool
  where
    newf :: Applicative m => Normal m -> Normal m -> m (Normal m)
    newf (PrimVal (Bool b1)) (PrimVal (Bool b2)) =
      pure $ PrimVal $ Bool $ f b1 b2


mkBoolSing :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => (Bool -> Bool) -> Normal m
mkBoolSing f = 
  liftFun newf (NormArr bool_t bool_t)
  where
    newf :: Applicative m => Normal m -> m (Normal m)
    newf (PrimVal (Bool b)) =
      pure $ PrimVal $ Bool $ f b


intSignature :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
intSignature =
  let binIntTy = NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T"))
      binIntCmp = NormArr (mkVar "T") (NormArr (mkVar "T") (PrimType BoolT))
        in
    NormSig [ ("T", NormUniv 0)
            , ("ℤ", NormUniv 0)
            , ("+", binIntTy)
            , ("-", binIntTy)
            , ("✕", binIntTy)
            , ("quot", binIntTy)
            , ("rem", binIntTy)
            , ("add-inv", NormArr (mkVar "T") (mkVar "T"))
             
            , ("^", mkIntOp (^))
             
            , ("e0", (mkVar "T"))
            , ("e1", (mkVar "T"))
             
            , ("show", NormArr (mkVar "T") (PrimType StringT))
             
            , ("=", binIntCmp)
            , ("≠", binIntCmp)
            , ("<", binIntCmp)
            , ("≤", binIntCmp)
            , (">", binIntCmp)
            , ("≥", binIntCmp)
            ]

intStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Normal m)]
intStructure = 
  [ ("T", int_t)
  , ("ℤ", int_t)
  , ("+", mkIntOp (+))
  , ("-", mkIntOp (-))
  , ("✕", mkIntOp (*))
  , ("quot", mkIntOp (quot))
  , ("rem", mkIntOp (rem))
  , ("add-inv", mkIntUni (\x -> -x))
   
  , ("^", mkIntOp (^))
   
  , ("e0", PrimVal (Int 0))
  , ("e1", PrimVal (Int 1))
   
  , ("show", intShow)
   
  , ("<", mkCmpOp (<))
  , ("≤", mkCmpOp (<=))
  , (">", mkCmpOp (>))
  , ("≥", mkCmpOp (>=))
  , ("=", mkCmpOp (==))
  , ("≠", mkCmpOp (/=))
  ]

floatSignature :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
floatSignature =
  let binFltTy = NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T"))
      binFltCmp = NormArr (mkVar "T") (NormArr (mkVar "T") (PrimType BoolT))
        in
    NormSig [ ("T", NormUniv 0)
            , ("Float", NormUniv 0)
            , ("+", binFltTy)
            , ("-", binFltTy)
            , ("✕", binFltTy)
            , ("÷", binFltTy)
            , ("^", binFltTy)
           
            , ("e0", mkVar "T")
            , ("e1", mkVar "T")
           
            , ("show", NormArr (mkVar "T") (PrimType StringT))
           
            ,  ("=", binFltCmp)
            ,  ("≠", binFltCmp)
            ,  ("<", binFltCmp)
            ,  ("≤", binFltCmp)
            ,  (">", binFltCmp)
            ,  ("≥", binFltCmp)
            ]

floatStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Normal m)] 
floatStructure =
   [ ("T",     float_t)
   , ("Float", float_t)
   , ("+", mkFloatOp (+))
   , ("-", mkFloatOp (-))
   , ("✕", mkFloatOp (*))
   , ("÷", mkFloatOp (/))
   , ("^", mkFloatOp (**))

   , ("e0", PrimVal (Float 0.0))
   , ("e1", PrimVal (Float 1.0))
   
   , ("add-inv", mkFloatUni (\x -> -x))
   , ("mul-inv", mkFloatUni (\x -> 1/x))
   , ("show", floatShow)

   , ("=", mkFltCmp (==))
   , ("≠", mkFltCmp (/=))
   , ("<", mkFltCmp (<))
   , ("≤", mkFltCmp (<=))
   , (">", mkFltCmp (>))
   , ("≥", mkFltCmp (>=))
   ]

  
boolFields :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => [(String, Normal m)] 
boolFields =
   [ ("∧", mkBoolOp (&&))
   , ("∨", mkBoolOp (||))
   , ("⊻", mkBoolOp (/=))
   , ("not", mkBoolSing not)
   ]

numSignature :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
numSignature = NormSig
               [ ("int", intSignature)
               , ("float", floatSignature)
               ]

numStructure :: (MonadReader (Environment m) m, MonadState (ProgState m) m, MonadError String m) => Normal m
numStructure = NormSct (toEmpty
               [ ("int", NormSct (toEmpty intStructure) intSignature)
               , ("float", NormSct (toEmpty floatStructure) floatSignature)
               ]) numSignature
  

binfloat = NormArr float_t (NormArr float_t float_t)
unifloat = NormArr float_t float_t
floatCompare = NormArr float_t (NormArr float_t bool_t)
  
binint = NormArr int_t (NormArr int_t int_t)
uniint = NormArr int_t int_t
intcompare = NormArr int_t (NormArr int_t bool_t)

unibool = NormArr bool_t bool_t
binbool = NormArr bool_t (NormArr bool_t bool_t)
