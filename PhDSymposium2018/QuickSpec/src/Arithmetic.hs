{-# LANGUAGE GADTs #-}
module Arithmetic where

import Test.QuickCheck
import Test.QuickSpec

data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

plus :: Nat -> Nat -> Nat
plus Zero     y = y
plus (Succ x) y = Succ (plus x y)

sig :: Sig
sig = signature [
    fun0 "zero"  Zero
  , fun1 "succ"  Succ
  , fun2 "plus"  plus
  , fun2 "equal" ((==) :: Nat -> Nat -> Bool)
  , fun2 "and"   (&&)
  , vars ["x", "y", "z"] (undefined :: Nat)
  , vars ["a", "b", "c"] (undefined :: Bool)
  ]








instance Eq Nat where
  Zero     == Zero     = True
  (Succ x) == (Succ y) = x == y
  x        == y        = False

instance Ord Nat where
  Zero   <= y      = True
  Succ x <= Succ y = x <= y
  x      <= y      = False

instance Arbitrary Nat where
  arbitrary = oneof [pure Zero, fmap Succ arbitrary]
