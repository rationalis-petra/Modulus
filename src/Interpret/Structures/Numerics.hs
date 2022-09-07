module Interpret.Structures.Numerics (numStructure) where

import Control.Monad.Except (throwError, catchError)

import qualified Data.Map as Map

import Data
import Data.Text (pack)
import Interpret.Eval (liftFun, liftFun2)
import Interpret.Transform

int_t = PrimType IntT
bool_t = PrimType BoolT
float_t = PrimType FloatT

floatShow :: Normal  
floatShow = liftFun newf (NormArr float_t (PrimType StringT))
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Float f)) = pure (PrimVal (String (pack (show f))))
    newf x =
      lift $ throwError ("bad arg to inbuilt float function" <> show x)

mkFloatUni :: (Float -> Float) -> Normal
mkFloatUni f = 
  liftFun newf unifloat
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Float f1)) =
      pure $ PrimVal $ Float $ f f1
    newf x =
      lift $ throwError ("bad arg to inbuilt float function" <> show x)


mkFloatOp :: (Float -> Float -> Float) -> Normal
mkFloatOp f = 
  liftFun2 newf binfloat
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Float f1)) (PrimVal (Float f2)) =
      pure $ PrimVal $ Float $ f f1 f2
    newf x y =
      lift $ throwError ("bad arg to inbuilt float function"
                         <> show x <> ", " <> show y)

mkFltCmp :: (Float -> Float -> Bool) -> Normal
mkFltCmp f = 
  liftFun2 newf floatCompare
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Float n1)) (PrimVal (Float n2)) =
      pure $ PrimVal $ Bool $ f n1 n2
    newf x y =
      lift $ throwError ("bad arg to inbuilt integer function " 
                         <> show x <> ", " <> show y)

intShow :: Normal  
intShow = liftFun newf (NormArr int_t (PrimType StringT))
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Int n1)) = pure (PrimVal (String (pack (show n1))))
    newf x =
      lift $ throwError ("bad arg to inbuilt float function" <> show x)
  
mkIntUni :: (Integer -> Integer) -> Normal
mkIntUni f = 
  liftFun newf uniint
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Int n1)) =
      pure $ PrimVal $ Int $ f n1
    newf x =
      lift $ throwError ("bad arg to inbuilt float function" <> show x)

mkIntOp :: (Integer -> Integer -> Integer) -> Normal
mkIntOp f = 
  liftFun2 newf binint
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Int n1)) (PrimVal (Int n2)) =
      pure $ PrimVal $ Int $ f n1 n2
    newf x y =
      lift $ throwError ("bad arg to inbuilt integer function"
                         <> show x <> ", " <> show y)

mkCmpOp :: (Integer -> Integer -> Bool) -> Normal
mkCmpOp f = 
  liftFun2 newf intcompare
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Int n1)) (PrimVal (Int n2)) =
      pure $ PrimVal $ Bool $ f n1 n2
    newf x y =
      lift $ throwError ("bad arg to inbuilt integer function"
                         <> show x <> ", " <> show y)

mkBoolOp :: (Bool -> Bool -> Bool) -> Normal
mkBoolOp f = 
  liftFun2 newf binbool
  where
    newf :: Normal -> Normal -> EvalM Normal
    newf (PrimVal (Bool b1)) (PrimVal (Bool b2)) =
      pure $ PrimVal $ Bool $ f b1 b2
    newf x y =
      lift $ throwError ("bad arg to inbuilt bool function"
                         <> show x <> ", " <> show y)

mkBoolSing :: (Bool -> Bool) -> Normal
mkBoolSing f = 
  liftFun newf (NormArr bool_t bool_t)
  where
    newf :: Normal -> EvalM Normal
    newf (PrimVal (Bool b)) =
      pure $ PrimVal $ Bool $ f b
    newf x =
      lift $ throwError ("bad arg to inbuilt bool function" <> show x)



intStructure :: [(String, Normal)]
intStructure = 
  [("t", int_t),
   ("Int", int_t),
   ("+", mkIntOp (+)),
   ("-", mkIntOp (-)),
   ("*", mkIntOp (*)),
   -- TODO: divide does not belong in a ring; but we want int to be a ring
   -- maybe?? 
   ("quot", mkIntOp (quot)),
   ("rem", mkIntOp (rem)),
   ("add-inv", mkIntUni (\x -> -x)),

   ("^", mkIntOp (^)),

   ("e0", PrimVal (Int 0)),
   ("e1", PrimVal (Int 1)),

   ("show", intShow),

   ("<", mkCmpOp (<)),
   ("≤", mkCmpOp (<=)),
   (">", mkCmpOp (>)),
   ("≥", mkCmpOp (>=)),
   ("=", mkCmpOp (==)),
   ("≠", mkCmpOp (/=))
  ]

floatStructure :: [(String, Normal)] 
floatStructure =
  [("t",     float_t),
   ("Float", float_t),
   ("+", mkFloatOp (+)),
   ("-", mkFloatOp (-)),
   ("*", mkFloatOp (*)),
   ("/", mkFloatOp (/)),
   ("^", mkFloatOp (**)),

   ("e0", PrimVal (Float 0.0)),
   ("e1", PrimVal (Float 1.0)),
   
   ("add-inv", mkFloatUni (\x -> -x)),
   ("mul-inv", mkFloatUni (\x -> 1/x)),

   ("<", mkFltCmp (<)),
   ("≤", mkFltCmp (<=)),
   (">", mkFltCmp (>)),
   ("≥", mkFltCmp (>=)),
   ("=", mkFltCmp (==)),
   ("≠", mkFltCmp (/=))
  ]

  
boolStructure :: [(String, Normal)] 
boolStructure =
  [("∧", mkBoolOp (&&)),
   ("∨", mkBoolOp (||)),
   ("⊻", mkBoolOp (/=)),
   ("not", mkBoolSing not)]

numStructure :: [(String, Normal)]
numStructure = 
  [("int", NormSct intStructure),
   ("float", NormSct floatStructure)
   ]

binfloat = NormArr float_t (NormArr float_t float_t)
unifloat = NormArr float_t float_t
floatCompare = NormArr float_t (NormArr float_t bool_t)
  
binint = NormArr int_t (NormArr int_t int_t)
uniint = NormArr int_t int_t
intcompare = NormArr int_t (NormArr int_t bool_t)

unibool = NormArr bool_t bool_t
binbool = NormArr bool_t (NormArr bool_t bool_t)
