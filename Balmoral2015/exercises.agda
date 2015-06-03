module exercises where

-- Ignore the man behind the curtain (for now!)
data Eq : {A B : Set} -> A -> B -> Set₁ where
  refl : {A : Set} -> {x : A} -> Eq x x

data Iso A B : Set₁ where
  iso : (f : A -> B) -> (g : B -> A)    ->
        ((x : A)     -> Eq x (g (f x))) ->
        ((y : B)     -> Eq y (f (g y))) ->
        Iso A B


-- *Non-dependent Types* --

-- Enumerations

-- Bottom is the empty type, containing no values
data Bottom : Set where

-- Unit has exactly one value
data Unit : Set where
  unit : Unit

-- There are exactly two Booleans
data Boolean : Set where
  True  : Boolean
  False : Boolean

-- Sums: If T1 contains N1 values and T2 contains N2 values, then Sum T1 T2
-- contains N1 + N2 values
data Sum A B : Set where
  Left  : A -> Sum A B
  Right : B -> Sum A B

-- Products: If T1 contains N1 values and T2 contains N2 values, then
-- Product T1 T2 contains N1 * N2 values
data Product A B : Set where
  pair : A -> B -> Product A B

-- Simple arithmetic

-- 1 + 1 = 2
boolean = Sum Unit Unit

{-
  The Natural numbers (following Peano's encoding):

  `Z`       represents 0
  `S Z`     represents 1
  `S (S Z)` represents 2

  In general, `S n` represents 'one more than n'
-}
data Nat : Set where
  Z : Nat
  S : Nat -> Nat

{-
  Make an encoding of the Integers, either from scratch or using some of the
  types above. In particular, your encoding should have these properties:

   - There should be no "negative zero"
   - It should not be possible to encode the same Integer in more than one way
-}

data WrongInteger : Set where
  wZ : WrongInteger
  wS : WrongInteger -> WrongInteger
  wP : WrongInteger -> WrongInteger -- Wrong, since S (P Z) == Z

data Integer : Set where
  Z : Integer
  Pos : Nat -> Integer
  Neg : Nat -> Integer

data Vector A : Nat -> Set where
  vNil  : Vector A Z
  vCons : {n : Nat} -> A -> Vector A n -> Vector A (S n)

plus : Nat -> Nat -> Nat
plus  Z    y = y
plus (S x) y = S (plus x y)

{-
succCong : (x y : Nat) -> Eq x y -> Eq (S x) (S y)
succCong  Z     Z    refl = refl
succCong (S x) (S y) p    with p
...| refl = {!!}
succCong  Z    (S y) ()
succCong (S x)  Z    ()

plusAssoc : (x y z : Nat) -> Eq (plus (plus x y) z)
                                (plus x (plus y z))
plusAssoc Z y z = refl
plusAssoc (S x) y z = {!!}
-}

vAppend : {A : Set} -> {m n : Nat} -> Vector A m -> Vector A n -> Vector A (plus m n)
vAppend  vNil        y = y
vAppend (vCons x x₁) y = vCons x (vAppend x₁ y)

{-
vAppendAssoc : {A : Set} -> {x y z : Nat}
                         -> (v1 : Vector A x)
                         -> (v2 : Vector A y)
                         -> (v3 : Vector A z)
                         -> Eq (vAppend (vAppend v1 v2) v3)
                               (vAppend v1 (vAppend v2  v3))
vAppendAssoc vNil v2 v3 = refl
vAppendAssoc (vCons x v1) v2 v3 = {!!}
-}

-- Write some functions!

-- Implement addition

-- Implement Maybe

-- Implement lists

-- Implement non-empty lists

-- Implement map for Maybe

-- Implement map for lists

-- Implement map for non-empty lists

-- Implement map for vectors

-- Implement map for pairs

-- Implement map for dependent pairs

-- Implement map for functions

-- Implement map for dependent functions

main : Nat
main = Z
