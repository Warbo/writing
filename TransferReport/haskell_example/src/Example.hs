module Example where
{-
type Nat = [()]

render :: Nat -> String
render = show . length

mult :: Nat -> Nat -> Nat
mult x y = case x of
                []     -> []
                ():as  -> y
                (a:as) -> y ++ mult as y

mult_tail' :: Nat -> Nat -> Nat -> Nat
mult_tail' x y acc = case x of
                          []     -> acc
                          (a:as) -> mult_tail' as y (y ++ acc)

mult_tail :: Nat -> Nat -> Nat
mult_tail x y = mult_tail' x y []
-}
factorial1 0 = 1
factorial1 n = n * factorial1 (n-1)

base      f = f 0    ==    f 1
increases f = f 4    >     f 3
divides   f = f 5    `div` f 4 == 5
negative  f = f (-1) ==    f 1

factorial2 0 = 1
factorial2 n = let nPos = abs n
                in nPos * factorial2 (nPos - 1)

f1_tail :: Int -> Int
f1_tail = go 1
  where go acc 0 = acc
        go acc n = go (n*acc) (n-1)

f2_tail :: Int -> Int
f2_tail = go 1
  where go acc 0 = acc
        go acc n = let nPos = abs n in go (nPos*acc) (nPos-1)

f1 :: Int -> Int
f1 = factorial1

f2 :: Int -> Int
f2 = factorial2

foo n = -n
