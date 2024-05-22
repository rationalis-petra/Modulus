module Typecheck.Unify where

-- This unification algorithm is based on the paper: 
--
-- Practical Dependent Type Checking Using Twin types
-- 
-- by Víctor López Juan and Nils Anders Danielsson  


-- Higher order unification uses 'metavariables' which can participate in
-- substitution. These are distinct from normal variables, and so we use a
-- decorated version of the Normal

