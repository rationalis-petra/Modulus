module Interpret.Structures.Structures where

import qualified Data.Map as Map
import Interpret.Structures.BuildStructure
import Data(Normal, Normal'(Undef), EvalM)

  
ringSource = "\
\ (signature \
\  (def t type)  \
\ \
\  (def e0 t) \
\  (def e1 t) \
\ \
\  (def `*` (t → t → t)) \
\  (def `+` (t → t → t)) \
\  (def `-` (t → t → t)) \
\ \
\  (def add-inv (t → t))) \
\"

fieldSource = "\
\ (signature \
\  (def t type)  \
\ \
\  (def e0 t) \
\  (def e1 t) \
\ \
\  (def `*` (t → t → t)) \
\  (def `+` (t → t → t)) \
\  (def `-` (t → t → t)) \
\  (def `/` (t → t → t)) \
\ \
\  (def add-inv (t → t)) \
\  (def mul-inv (t → t))) \
\"

implFieldSource = "\
\ (module \
\ \
\  (defn `*` {F : Field} [(n1 : F.t) (n2 : F.t)]\
\     (F.`*` n1 n2)) \
\  (defn `+` {F : Field} [(n1 : F.t) (n2 : F.t)]\
\     (F.`+` n1 n2)) \
\  (defn `-` {F : Field} [(n1 : F.t) (n2 : F.t)]\
\     (F.`-` n1 n2)) \
\  (defn `/` {F : Field} [(n1 : F.t) (n2 : F.t)]\
\     (F.`/` n1 n2)) \
\ \
\  (defn add-inv {F : Field} [(n : F.t)] (F.add-inv n)) \
\  (defn mul-inv {F : Field} [(n : F.t)] (F.mul-inv n))) \
\"

fieldSig :: EvalM Normal
fieldSig = buildModule Map.empty fieldSource

ringSig :: EvalM Normal
ringSig = do
  buildModule Map.empty ringSource


structStructure :: EvalM [(String, Normal)]
-- structModule = do
--   sfield <- fieldSig
--   sring <- ringSig
--   pure $ Map.fromList [("Ring",  sring),
--                        ("Field", sfield)]

structStructure = pure []