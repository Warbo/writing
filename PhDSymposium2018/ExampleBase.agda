 module Example where

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

one two three : Nat
one   = Succ Zero
two   = Succ one
three = Succ two

plus : Nat -> Nat -> Nat
plus Zero     y = y
plus (Succ x) y = Succ (plus x y)

data Equal : Nat -> Nat -> Set where
  reflexivity : (x : Nat) -> Equal x x

data And (a b : Set) : Set where
  and : a -> b -> And a b

commute : (x y : Nat) -> Equal (plus x y) (plus y x)
commute x y = ?

























-- plusZero : (x : Nat) -> Equal x (plus x Zero)
-- plusZero x = ?



























-- cong : {x y : Nat} -> Equal x y -> Equal (Succ x) (Succ y)
-- cong p = ?





























-- plusSucc : (x y : Nat) -> Equal (Succ (plus x y)) (plus x (Succ y))
-- plusSucc x y = ?


























-- trans : {x y z : Nat} -> And (Equal x y) (Equal y z) -> Equal x z
-- trans p = ?
