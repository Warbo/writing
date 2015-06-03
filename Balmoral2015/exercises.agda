module exercises where

-- *Technical Stuff* --

-- For the moment, don't worry about *how* these two work, just what they mean

-- "Eq foo bar" means the terms "foo" and "bar" are the same

-- START EX Eq_def
data Eq : {A B : Set} -> A -> B -> Set₁ where
  refl : {A : Set} -> {x : A} -> Eq x x
-- END EX Eq_def

-- "Iso Foo Bar" means the types "Foo" and "Bar" are isomorphic (we can convert
-- values back and forth between them)
data Iso A B : Set₁ where
  iso : (f : A -> B) -> (g : B -> A)    ->
        ((x : A)     -> Eq x (g (f x))) ->
        ((y : B)     -> Eq y (f (g y))) ->
        Iso A B

-- *Examples and Exercises* --

-- We start with some easy non-dependent types

-- Enumerations: types with a finite number of elements

-- Bottom is the empty type, containing no values
data Bottom : Set where

-- Unit has exactly one value
data Unit : Set where
  unit : Unit

-- There are exactly two Booleans
data Boolean : Set where
  True  : Boolean
  False : Boolean

-- We can do this for any number of values.

-- Exercise: Define a type Direction containing values Up, Down, Left and Right

-- We can define "higher-order" types

-- Sums: If T1 contains N1 values and T2 contains N2 values, then Sum T1 T2
-- contains N1 + N2 values
data Sum A B : Set where
  Left  : A -> Sum A B
  Right : B -> Sum A B

-- Products: If T1 contains N1 values and T2 contains N2 values, then
-- Product T1 T2 contains N1 * N2 values
data Prod A B : Set where
  pair : A -> B -> Prod A B

data DepProd A (f : A -> Set) : Set where
  dpair : (x : A) -> (p : f x) -> DepProd A f

{-
  The Natural numbers (following Peano's encoding):

  `Z`       represents 0
  `S Z`     represents 1
  `S (S Z)` represents 2

  In general, `S n` represents 'one more than n'
-}

-- START EX Nat_def
data Nat : Set where
  Z : Nat
  S : Nat -> Nat

add : Nat -> Nat -> Nat
add x  Z    = x
add x (S y) = S (add x y)
-- END EX Nat_def

-- This lets us write `0`, `1`, etc. instead of `Z`, `S Z`, etc.
{-# BUILTIN NATURAL Nat #-}

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

-- This stops Agda complaining
postulate IO : Set -> Set
postulate io : Nat -> IO Nat
{-# BUILTIN IO IO #-}
main : IO Nat
main = io Z

-- Some more complex experiments

plus : Nat -> Nat -> Nat
plus  Z    y = y
plus (S x) y = S (plus x y)

succCong : (x y : Nat) -> Eq x y -> Eq (S x) (S y)
succCong x .x refl = refl

plusZ : (n : Nat) -> Eq n (plus n Z)
plusZ Z = refl
plusZ (S n) = succCong n (plus n Z) (plusZ n)

plusS : (n m : Nat) -> Eq (plus (S n) m) (plus n (S m))
plusS Z m = refl
plusS (S n) m = succCong (S (plus n m)) (plus n (S m)) (plusS n m)

eqSym : {A : Set} -> {x y : A} -> Eq x y -> Eq y x
eqSym refl = refl

eqTrans : {A B C : Set} -> {x : A} -> {y : B} -> {z : C} -> Eq x y -> Eq y z -> Eq x z
eqTrans refl refl = refl

plusStep : (x y : Nat) -> Eq (plus (S x) y) (S (plus x y))
plusStep x y = refl

plusSucc : (x y : Nat) -> Eq (plus (S x) y) (plus x (S y))
plusSucc Z y = refl
plusSucc (S x) y = succCong (S (plus x y)) (plus x (S y)) (plusSucc x y)

plusComm : (x y : Nat) -> Eq (plus x y) (plus y x)
plusComm Z Z = refl
plusComm Z (S y) = succCong y (plus y Z) (plusComm Z y)
plusComm (S x) Z = succCong (plus x Z) x (eqSym (plusZ x))
plusComm (S x) (S y) = succCong (plus x (S y)) (plus y (S x)) (eqTrans (plusComm x (S y)) (plusS y x))

plusAssoc : (x y z : Nat) -> Eq (plus (plus x y) z)
                                (plus x (plus y z))
plusAssoc Z y z = refl
plusAssoc (S x) y z = succCong (plus (plus x y) z) (plus x (plus y z)) (plusAssoc x y z)

plusEq : (x y z : Nat) -> Eq x y -> Eq (plus z x) (plus z y)
plusEq x .x z refl = refl

vAppend : {A : Set} -> {m n : Nat} -> Vector A m -> Vector A n -> Vector A (plus m n)
vAppend  vNil        y = y
vAppend (vCons x x₁) y = vCons x (vAppend x₁ y)

vConsCong : {A B : Set} -> {n m : _} -> {x : A} -> {y : B} -> {xs : Vector A n} -> {ys : Vector B m}
                        -> Eq x y -> Eq n m -> Eq xs ys -> Eq (vCons x xs) (vCons y ys)
vConsCong refl refl refl = refl

{-
vAppendNil : (xs : _) -> Eq (vAppend xs vNil) xs
vAppendNil vNil = refl

vConsEq : {A B : Set} -> {n m : Nat} -> {x : A} -> (xs : Vector A n) ->{y : B} -> (ys : Vector B m)
                      -> Eq (vCons x xs) (vCons y ys) -> Eq xs ys
vConsEq vNil vNil p = {!!}
vConsEq vNil (vCons x₁ ys) p = {!!}
vConsEq (vCons x₁ xs) ys p = {!!}

vLenEq : {n m : Nat} -> {A B : Set} -> (xs : Vector A n) -> (ys : Vector B m) -> Eq xs ys -> Eq n m
vLenEq vNil vNil p = refl
vLenEq vNil (vCons x ys) ()
vLenEq (vCons x xs) vNil ()
vLenEq (vCons x xs) (vCons x₁ ys) p = {!!}

vAppendCong : {A : Set} -> {x y z : Nat} -> (xs : Vector A x)
                                         -> (ys : Vector A y)
                                         -> (zs : Vector A z)
                                         -> Eq ys zs -> Eq (vAppend xs ys) (vAppend xs zs)
vAppendCong vNil ys zs p = p
vAppendCong (vCons x xs) ys zs p = {!!}

vAppendAssoc : {A : Set} -> {x y z : Nat}
                         -> (v1 : Vector A x)
                         -> (v2 : Vector A y)
                         -> (v3 : Vector A z)
                         -> Eq (vAppend (vAppend v1 v2) v3)
                               (vAppend v1 (vAppend v2  v3))
vAppendAssoc vNil v2 v3 = refl
vAppendAssoc (vCons x v1) vNil v3 = eqTrans {!vAppendCong!} {!!}
vAppendAssoc (vCons x v1) (vCons x₁ v2) v3 = {!!}
-}

-- Slide examples follow from here

-- START EX T_def
data T : Nat -> Nat -> Set where
  c1 : (n   : Nat)          -> T n    n
  c2 : {n m : Nat} -> T n m -> T n (S m)
-- END EX T_def

-- START EX T_vals
t1 : T 0 0
t1 = c1 0

t2 : T 0 1
t2 = c2 (c1 0)

t3 : T 2 5
t3 = c2 (c2 (c2 (c1 2)))
-- END EX T_vals

-- START EX LTE_def
data LTE : Nat -> Nat -> Set where
  eq : (n   : Nat)            -> LTE n    n
  lt : {n m : Nat} -> LTE n m -> LTE n (S m)
-- END EX LTE_def

-- START EX LTE_vals
lte1 : LTE 0 0
lte1 = eq 0

lte2 : LTE 0 1
lte2 = lt (eq 0)

lte3 : LTE 2 5
lte3 = lt (lt (lt (eq 2)))
-- END EX LTE_vals

-- START EX LTE_trans
lteTrans : {a b c : Nat} ->
           LTE a b -> LTE b c -> LTE a c
lteTrans x (eq y) = x
lteTrans x (lt y) = lt (lteTrans x y)
-- END EX LTE_trans

-- START EX LTE_prop
l2N : {n m : Nat} -> LTE n m -> Nat
l2N (eq _) = Z
l2N (lt x) = S (l2N x)

lteProp : (n m : Nat) -> (d : LTE n m) ->
          Eq m (plus n (l2N d))
-- END EX LTE_prop

lteProp n .n (eq .n) = plusZ n
lteProp n (S m) (lt d) = eqSym (eqTrans (plusComm n (S (l2N d))) (succCong (plus (l2N d) n) m (eqTrans (plusComm (l2N d) n) (eqSym (lteProp n m d)))))

-- START EX DPair_def
data DPair : (T1 : _) -> (T2 : T1 -> Set₁) ->
             Set₂ where
  dpair : {T1 : Set} -> {T2 : T1 -> Set₁} ->
          (x : T1) -> (p : T2 x) -> DPair T1 T2
-- END EX DPair_def

-- START EX LTE2_def
lte2Prop : Nat -> Nat -> Nat -> Set₁
lte2Prop n m d = Eq m (plus n d)

LTE2 : Nat -> Nat -> Set₂
LTE2 n m = DPair Nat (lte2Prop n m)
-- END EX LTE2_def

-- START EX LTE2_vals
d1 : LTE2 0 0
d1 = dpair 0 refl

d2 : LTE2 0 1
d2 = dpair 1 refl

d3 : LTE2 2 5
d3 = dpair 3 refl
-- END EX LTE2_vals

-- START EX Curry_def
curry : {A : Set} -> {F : A -> Set₁} ->
        {P : DPair A F -> Set} ->
        (g : (p : DPair A F) -> P p) ->
        (a : A) -> (f : F a) ->
        P (dpair a f)
curry g a f = g (dpair a f)
-- END EX Curry_def

-- START EX Curry_one
func1 : (n m : Nat) -> LTE2 n m -> Nat
func1 n m (dpair d p) = plus m (plus n d)

func2 : (n m d : Nat) -> lte2Prop n m d -> Nat
func2 n m d p = plus m (plus n d)

func1Prop : (n m : Nat) -> (d : LTE2 n m) ->
            Eq (func1 n m d) (plus m m)
func1Prop n .(plus n d) (dpair d refl) = refl

func2Prop : (n m d : Nat) ->
            (p : lte2Prop n m d) ->
            Eq (func2 n m d p) (plus m m)
func2Prop n .(plus n d) d refl = refl
-- END EX Curry_one

tag : Nat -> Set
tag 0 = Nat
tag 1 = Boolean
tag _ = Bottom

--id : {a : _} -> a -> a
--id x = x

--dyn1 : DPair Set id
--dyn1 = dpair Nat 0
