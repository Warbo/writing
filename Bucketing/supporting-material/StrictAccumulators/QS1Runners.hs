module Runners where

import Defs
import Test.QuickSpec

vs = map (gvars ["nat1", "nat2", "nat3"]) [g, g, g]
  where g = arbitrary :: Gen Nat

[qs_mult2_lazy, qs_mult2_strict, qs_plus_lazy] = map (quickSpec . (:vs))
  [ fun3 "mult2_lazy"   mult2_lazy
  , fun3 "mult2_strict" mult2_strict
  , fun2 "plus_lazy"    plus
  ]
