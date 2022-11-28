module Syntax.Core (Core(..),
                    TopCore(..),
                    Definition(..),
                   ) where

import Syntax.Normal (Normal(..), CoPattern(..), Pattern(..))


data Core m
  = CNorm (Normal m)                                 -- Normalised value
  | CVar String                                      -- Variable
  | CDot (Core m) String                             -- Access a field from a struct/signature
  | CArr (Core m) (Core m)                           -- Arrow Type (degenerate product)
  | CProd String (Core m) (Core m)                   -- Dependent Product 
  | CImplProd String (Core m) (Core m)               -- Dependent Product 
  | CAbs String (Core m) (Normal m)                  -- Function abtraction
  | CApp (Core m) (Core m)                           -- Function application 
  | CMAbs String (Normal m) (Core m)                 -- Macro abstraction
  | CLet [(String, Core m)] (Core m) (Normal m)      -- Local binding
  | CMatch (Core m) [(Pattern m, Core m)] (Normal m) -- Pattern-Match
  | CCoMatch [(CoPattern m, Core m)] (Normal m)      -- Pattern-Comatch (for coinductive types)

  -- TODO: remove this via lazy functions (induction?!)
  | CIf (Core m) (Core m) (Core m) (Normal m)   -- Conditional 
  | CSct [Definition m] (Normal m)              -- Structure Definition
  | CSig [Definition m]                         -- Signature Definition (similar to dependent sum)

  -- TODO: plugin
  -- TODO: we want compile-time + run-time variants!
  | CAdaptForeign String String [(String, String, Normal m)]
  deriving Show


data TopCore m = TopDef (Definition m) | TopExpr (Core m) | TopAnn String (Core m)
  deriving Show


data Definition m
  = SingleDef   String (Core m) (Normal m)
  | InductDef   String Int [(String, Normal m)] (Normal m) (Normal m) [(String, Int, Normal m)] 
  | CoinductDef String Int [(String, Normal m)] (Normal m) (Normal m) [(String, Int, Normal m)] 
  | OpenDef (Core m) [(String, Normal m)]
  deriving Show
