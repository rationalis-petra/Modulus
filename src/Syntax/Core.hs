module Syntax.Core (Core(..),
                    TopCore(..),
                    Definition(..),
                   ) where

import Data (Normal, Normal(..), CoPattern(..), Pattern(..))


data Core
  = CNorm Normal                           -- Normalised value
  | CVar String                            -- Variable
  | CDot Core String                       -- Access a field from a struct/signature
  | CArr Core Core                         -- Arrow Type (degenerate product)
  | CProd String Core Core                 -- Dependent Product 
  | CImplProd String Core Core             -- Dependent Product 
  | CAbs String Core Normal                -- Function abstraction
  | CApp Core Core                         -- Function application 
  | CMAbs String Normal Core               -- Macro abstraction
  | CLet [(String, Core)] Core Normal      -- Local binding
  | CMatch Core [(Pattern, Core)] Normal   -- Pattern-Match
  | CCoMatch [(CoPattern, Core)] Normal    -- Pattern-Comatch (for coinductive types)

  -- TODO: remove this via lazy functions (induction?!)
  | CIf Core Core Core Normal              -- Conditional 
  | CSct [Definition] Normal               -- Structure Definition
  | CSig [Definition]                      -- Signature Definition (similar to dependent sum)

  -- TODO: plugin
  -- TODO: we want compile-time + run-time variants!
  | CAdaptForeign String String [(String, String, Normal)]
  deriving Show


data TopCore = TopDef Definition | TopExpr Core | TopAnn String Core
  deriving Show


data Definition
  = SingleDef String Core Normal
  | InductDef   String Int [(String, Normal)] Normal Normal [(String, Int, Normal)] 
  | CoinductDef String Int [(String, Normal)] Normal Normal [(String, Int, Normal)] 
  | OpenDef Core [(String, Normal)]
  deriving Show
