module Interpret.Structures.Numerics (numStructure, numSignature) where

import qualified Data.Map as Map

import Data
import Data.Text (pack)
import Interpret.EvalM (throwError)
import Interpret.Eval (liftFun, liftFun2)
import Interpret.Transform

int_t = PrimType IntT
bool_t = PrimType BoolT
float_t = PrimType FloatT

mkVar s = (Neu (NeuVar s (NormUniv 0)) (NormUniv 0))

floatShow :: Normal  
floatShow = liftFun newf (NormArr float_t (PrimType StringT))
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Float f)) = pure (PrimVal (String (pack (show f))))

mkFloatUni :: (Float -> Float) -> Normal
mkFloatUni f = 
  liftFun newf unifloat
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Float f1)) = pure $ PrimVal $ Float $ f f1


mkFloatOp :: (Float -> Float -> Float) -> Normal
mkFloatOp f = 
  liftFun2 newf binfloat
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Float f1)) (PrimVal (Float f2)) =
      pure $ PrimVal $ Float $ f f1 f2

mkFltCmp :: (Float -> Float -> Bool) -> Normal
mkFltCmp f = 
  liftFun2 newf floatCompare
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Float n1)) (PrimVal (Float n2)) =
      pure $ PrimVal $ Bool $ f n1 n2

intShow :: Normal  
intShow = liftFun newf (NormArr int_t (PrimType StringT))
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Int n1)) = pure (PrimVal (String (pack (show n1))))
  
mkIntUni :: (Integer -> Integer) -> Normal
mkIntUni f = 
  liftFun newf uniint
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Int n1)) = pure $ PrimVal $ Int $ f n1

mkIntOp :: (Integer -> Integer -> Integer) -> Normal
mkIntOp f = 
  liftFun2 newf binint
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Int n1)) (PrimVal (Int n2)) =
      pure $ PrimVal $ Int $ f n1 n2

mkCmpOp :: (Integer -> Integer -> Bool) -> Normal
mkCmpOp f = 
  liftFun2 newf intcompare
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Int n1)) (PrimVal (Int n2)) =
      pure $ PrimVal $ Bool $ f n1 n2

mkBoolOp :: (Bool -> Bool -> Bool) -> Normal
mkBoolOp f = 
  liftFun2 newf binbool
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Bool b1)) (PrimVal (Bool b2)) =
      pure $ PrimVal $ Bool $ f b1 b2

mkBoolSing :: (Bool -> Bool) -> Normal
mkBoolSing f = 
  liftFun newf (NormArr bool_t bool_t)
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Bool b)) =
      pure $ PrimVal $ Bool $ f b


intSignature :: Normal
intSignature =
  let binIntTy = NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T"))
      binIntCmp = NormArr (mkVar "T") (NormArr (mkVar "T") (PrimType BoolT))
        in
    NormSig [ ("T", NormUniv 0)
            , ("ℤ", NormUniv 0)
            , ("+", binIntTy)
            , ("-", binIntTy)
            , ("⋅", binIntTy)
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

intStructure :: [(String, Normal)]
intStructure = 
  [ ("t", int_t)
  , ("ℤ", int_t)
  , ("+", mkIntOp (+))
  , ("-", mkIntOp (-))
  , ("⋅", mkIntOp (*))
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

floatSignature :: Normal
floatSignature =
  let binFltTy = NormArr (mkVar "T") (NormArr (mkVar "T") (mkVar "T"))
      binFltCmp = NormArr (mkVar "T") (NormArr (mkVar "T") (PrimType BoolT))
        in
    NormSig [ ("t", NormUniv 0)
            , ("Float", NormUniv 0)
            , ("+", binFltTy)
            , ("-", binFltTy)
            , ("⋅", binFltTy)
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

floatStructure :: [(String, Normal)] 
floatStructure =
   [ ("t",     float_t)
   , ("Float", float_t)
   , ("+", mkFloatOp (+))
   , ("-", mkFloatOp (-))
   , ("⋅", mkFloatOp (*))
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

  
boolStructure :: [(String, Normal)] 
boolStructure =
   [ ("∧", mkBoolOp (&&))
   , ("∨", mkBoolOp (||))
   , ("⊻", mkBoolOp (/=))
   , ("not", mkBoolSing not)
   ]

numSignature :: Normal  
numSignature = NormSig
               [ ("int", intSignature)
               , ("float", floatSignature)
               ]

numStructure :: Normal
numStructure = NormSct
               [ ("int", NormSct intStructure intSignature)
               , ("float", NormSct floatStructure floatSignature)
               ] numSignature

  

binfloat = NormArr float_t (NormArr float_t float_t)
unifloat = NormArr float_t float_t
floatCompare = NormArr float_t (NormArr float_t bool_t)
  
binint = NormArr int_t (NormArr int_t int_t)
uniint = NormArr int_t int_t
intcompare = NormArr int_t (NormArr int_t bool_t)

unibool = NormArr bool_t bool_t
binbool = NormArr bool_t (NormArr bool_t bool_t)
