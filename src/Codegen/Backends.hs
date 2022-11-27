module Codegen.Backends where 


-- submodules

-- Define an interface to execution backends. There are several considerations
-- when desiging backends 

-- Considerations
-- + Bakends can support being Interpretet/evaluated at Runtime
--   + When doing so they should have a 'runtime environment' that represents
--     current threads, variable bindings etc.
--   + When doing so they should export some notion of 'capabilities', i.e. 
--     they export somehow things they are and are not capable of
--   + When doign so, they should have to options for evaluation
--     + eval-to-value
--     + eval-to-io
-- + Backends can support being compiled, but not executed
--   + Backends may be able to output to/read from files when compiling

-- + Backends should be conscious of the module hierarchy
--   + Backends have concepts of a module and an environment (module tree) and  
--   + Definitions always take place in a module
--   + 



-- TODO: type families??
-- e is a 'compiled expression'
-- t is a compiled module tree 
-- m: a monad transformer the 'execution environment'
-- we probably want different monads for compilation vs execution (ignore for now) 
-- class Backend e t m where 
--   compileModule :: [String] -> [Definition] -> m Identity t
--   compileExpr :: [String] -> Core -> m Identity e
--   
--   eval :: [String] -> a -> m IO Normal
  
