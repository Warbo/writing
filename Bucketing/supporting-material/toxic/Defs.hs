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

smallGen = i2n <$> choose (0, 2)

-- Helper functions

plus :: Nat -> Nat -> Nat
plus x y = case x of
             Z   -> y
             S z -> S (plus z y)

mult x y = case x of
             Z   -> Z
             S z -> plus y (mult z y)

-- Functions to explore

mult2_lazy, mult2_strict :: Nat -> Nat -> Nat -> Nat
mult2_lazy x y z = case x of
                     Z    -> z
                     S x2 -> mult2_lazy x2 y (plus y z)

mult2_strict x y !z = case x of
                        Z    -> z
                        S x2 -> mult2_strict x2 y (plus y z)

qexp_lazy, qexp_strict :: Nat -> Nat -> Nat -> Nat
qexp_lazy x y z = case y of
                    Z   -> z
                    S n -> qexp_lazy x n (mult x z)

qexp_strict x y !z = case y of
                       Z   -> z
                       S n -> qexp_strict x n (mult x z)

op_lazy, op_strict :: Nat -> Nat -> Nat -> Nat -> Nat
op_lazy x y z x2 = case x of
                     Z    -> case z of
                               Z    -> x2
                               S x3 -> op_lazy Z  y x3 (S x2)
                     S x4 -> case z of
                               Z    -> op_lazy x4 y y     x2
                               S c  -> op_lazy x  y c  (S x2)

op_strict x y z x2 = case x of
                       Z    -> case z of
                                 Z    -> x2
                                 S x3 -> op_strict Z  y x3 (S x2)
                       S x4 -> case z of
                                 Z    -> op_strict x4 y y     x2
                                 S c  -> op_strict x  y c  (S x2)
