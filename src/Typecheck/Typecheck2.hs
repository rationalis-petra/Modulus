module Typecheck.Typecheck2 where

import qualified Data.Map as Map
import qualified Data.Set as Set



-- data InfType 
--   = ITypeN Int
--   | JMVar (Either String Int)
--   | IMSig (Map.Map String InfType)
--   | IMArr InfType InfType
--   | IMDep InfType String InfType
--   | IImplMDep InfType String InfType
--   | IMDot InfType String
--   | IMEffect (Set.Set EffectType)
--   --        id  name   params        instance-types           
--   | IMNamed Int String [InfType] [[InfType]]

--   -- "Primitive" / native types
--   | IMPrim PrimType
--   | IMVector InfType


-- Subst = Map.Map Int InfType -- substitution
-- App = InfType -- implicit type application

-- unify :: InfType -> InfType -> Subst
-- unify (ImplMDep )

-- lunify :: InfType -> TIntermediate -> InfType -> (TIntermediate, Subst)

-- runify :: InfType  -> InfType -> TIntermediate -> (Subst, TIntermediate)

-- lrunify :: InfType -> TIntermediate-> InfType -> TIntermediate -> (TIntermediate, Subst, TIntermediate)
  



-- toInfType :: ModulusType -> InfType 







