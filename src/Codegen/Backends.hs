module Codegen.Backends where 


-- submodules

-- Define an interface to execution backends. There are several considerations
-- when desiging backends 

-- Considerations
-- + Bakends can support being Interpretet/evaluated at Runtime
--   + When doing so they should have a 'runtime environment'
--   + When doing so they should export some notion of 'capabilities'
--   + When doign so, they should have to options for evaluation
--     + eval-to-value
--     + eval-to-io
-- + Backends can support being compiled
--   + Backends may be able to output to/read from files when compiling

-- + Backends should be conscious of the module hierarchy
--   + Backends have concepts of a module and an environment (module tree) and  
--   + Definitions always take place in a module
--   + 


-- TODO: type families??
-- class Backend e m where 
--    :: [Definition] -> a
--    :: 
--    :: [Core] -> ?

--   -- 
--   evaluate :: [String] -> a -> [Core]
  
