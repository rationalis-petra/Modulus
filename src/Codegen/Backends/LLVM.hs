module Codegen.Backends.LLVM where

import LLVM.Core
import Syntax.Core



-- A modulus module is notionally a pair (llvm-module, data) where the 'data'
-- field notionally contains metadata 
data MlsModule 
  = MlsModule { llvmModule :: Module
              , modulePath :: [String]
              -- , (types) :: []
              -- , (ctors) :: []
              -- , (dtors) :: []
              -- , (sigs/structs) :: []
              }


-- note: values of type IO a are represented as functions void → llvm<a>


  

compileModule :: [String] -> [Definition m] -> IO MlsModule
compileModule path defs = do
  mdle <- newModule
  pure $ MlsModule mdle path

-- compileDef :: Definition -> 
compileDef _ _ = do
  putStrLn "compile module not implemented definitions that aren't singledef"
  


-- if compilation encounters lambdas in a
--compile :: Core -> ??
compile (CIf cond trueBranch falseBranch _) = do
  ifTrue <- newBasicBlock
  ifFalse <- newBasicBlock
  fnlBB <- newBasicBlock 
  
  cond' <- compile cond
  condBr cond' ifTrue ifFalse
  
   
  defineBasicBlock ifTrue
  val1 <- compile trueBranch

  defineBasicBlock ifFalse
  val2 <- compile falseBranch

  -- join two execution paths 
  defineBasicBlock fnlBB
  phi [(val1, ifTrue), (val2, ifFalse)]


