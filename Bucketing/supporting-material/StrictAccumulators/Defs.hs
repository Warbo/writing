{-# LANGUAGE BangPatterns #-}
module Defs where

import Test.QuickCheck
import Test.QuickSpec

-- Peano numerals

data Nat = Z | S Nat deriving (Eq)

i2n :: Integer -> Nat
i2n 0 = Z
i2n n = S (i2n (abs n - 1))

n2i :: Nat -> Integer
n2i  Z    = 0
n2i (S n) = 1 + n2i n

instance Show Nat where
  show = show . n2i

instance Ord Nat where
  Z   <= _   = True
  S x <= Z   = False
  S x <= S y = x <= y

instance Arbitrary Nat where
  arbitrary = i2n <$> arbitrary

plus :: Nat -> Nat -> Nat
plus  Z    y = y
plus (S x) y = S (plus x y)

mult2_lazy, mult2_strict :: Nat -> Nat -> Nat -> Nat
mult2_lazy x y z = case x of
                     Z    -> z
                     S x2 -> mult2_lazy x2 y (plus y z)

mult2_strict x y !z = case x of
                        Z    -> z
                        S x2 -> mult2_strict x2 y (plus y z)
