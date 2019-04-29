module Runners where

import Defs
import Test.QuickCheck
import Test.QuickSpec

vs = map (gvars ["nat1", "nat2", "nat3"]) [g, g, g]
  where g = arbitrary :: Gen Nat

[qs_mult2_lazy  ,
 qs_mult2_strict,
 qs_qexp_lazy   ,
 qs_qexp_strict ,
 qs_op_lazy     ,
 qs_op_strict   ] =
  map (quickSpec . (:vs)) [ fun3 "mult2_lazy"   mult2_lazy
                          , fun3 "mult2_strict" mult2_strict
                          , fun3 "qexp_lazy"    qexp_lazy
                          , fun3 "qexp_strict"  qexp_strict
                          , fun4 "op_lazy"      op_lazy
                          , fun4 "op_strict"    op_strict
                          ]

vsmall = map (gvars ["small1", "small2", "small3"]) [g, g, g]
  where g = smallGen

[small_mult2_lazy  ,
 small_mult2_strict,
 small_qexp_lazy   ,
 small_qexp_strict ,
 small_op_lazy     ,
 small_op_strict   ] =
  map (quickSpec . (:vsmall)) [ fun3 "mult2_lazy"   mult2_lazy
                              , fun3 "mult2_strict" mult2_strict
                              , fun3 "qexp_lazy"    qexp_lazy
                              , fun3 "qexp_strict"  qexp_strict
                              , fun4 "op_lazy"      op_lazy
                              , fun4 "op_strict"    op_strict
                              ]
