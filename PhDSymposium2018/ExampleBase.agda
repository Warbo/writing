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

---

data Equal : Nat -> Nat -> Set where
  reflexivity : (x : Nat) -> Equal x x

cong : {x y : Nat} -> (f : Nat -> Nat) -> Equal x y -> Equal (f x) (f y)
cong f (reflexivity x) = reflexivity (f x)

trans : {x y z : Nat} -> (Equal x y) -> (Equal y z) -> Equal x z
trans (reflexivity x) p2 = p2

plusZero : (x : Nat) -> Equal x (plus x Zero)
plusZero Zero     = reflexivity Zero
plusZero (Succ x) = cong Succ (plusZero x)

plusSucc : (x y : Nat) -> Equal (Succ (plus x y)) (plus x (Succ y))
plusSucc Zero     y = reflexivity (Succ y)
plusSucc (Succ x) y = cong Succ (plusSucc x y)

---

commute : (x y : Nat) -> Equal (plus x y) (plus y x)
commute x y = ?
