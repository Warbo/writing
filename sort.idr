




module Sort

-- Reference implementation

sort : (t -> t -> Bool) ->  -- Comparison function
       (List t)         ->  -- Input list
       (List t)             -- Sorted list
sort f []      = []
sort f (x::xs) = those (f x) ++ [x] ++ those (not . (f x))
                 where those o = sort f (filter o xs)

le : Int -> Int -> Bool
le = (<=)

testIn : List Int
testIn = [1, 5, 3, 2]

testOut : List Int
testOut = [5, 3, 2, 1]

sortCorrect : (sort le testIn = testOut)
sortCorrect = refl

------------------------
--  Dynamically typed --
------------------------

Dyn : Type
Dyn = (t : Type ** t)

sort0 : Dyn

-- No restrictions at all!

sort0 = (Int ** 5)

------------------------------------
-- Function between dynamic types --
------------------------------------

sort1 : Dyn -> Dyn

-- No meaningful restrictions

sort1 x = (Int ** 5)

----------------------------
-- Function between Lists --
----------------------------

sort2 : List Int -> List Int

-- We know how to make a 'List Int' regardless of input!

sort2 l = [1, 2, 3]

-----------------------
-- Polymorphic Lists --
-----------------------

sort3 : (t -> t -> Bool) ->  -- Comparison function
        (List t)         ->  -- Input list
        (List t)             -- Sorted list

-- We know how to make a 'List t' for all t!

sort3 f l = []

----------------------------------
-- Vectors: Lists with a length --
----------------------------------

sort4 : (t -> t -> Bool) ->  -- Comparison function
        (l : List t)     ->  -- Input list
        (Vect (length l) t)  -- Sorted vector, of same length

-- We can just convert the List to a Vector!

sort4 f []      = []
sort4 f (x::xs) = x :: (sort4 f xs)

myT : (t : Type) -> List t
myT t = []

--------------------------------------
-- Steps towards a sorted list type --
--------------------------------------

-- 'Sorted' depends on the comparison function

data WithFunc : Nat              ->  -- Length
                (t : Type)       ->  -- Element type
                (t -> t -> Bool) ->  -- Comparison function
                Type             where

  wfNil :  (f : t -> t -> Bool) ->  -- Given a comparison function
           (WithFunc 0 t f)         -- We can make an empty list

  wfCons : (x : t)          ->  -- Element to prepend
           (WithFunc n t f) ->  -- List, which provides comparison
           (WithFunc (S n) t f) -- Re-use comparison, increment length

-- Doesn't gain us much, we can still just convert the list

sort5 : (f : (t -> t -> Bool)) ->
        (l : List t)           ->
        (WithFunc (length l) t f)
sort5 f []      = wfNil f
sort5 f (x::xs) = wfCons x (sort5 f xs)

--------------------------------------
-- Restrict the comparison function --
--------------------------------------

-- Reflexivity: f x x = True

data Reflexive : (t : Type) -> (t -> t -> Bool) -> Type where
  reflexive : (t : Type)                  ->
              (f : t -> t -> Bool)        ->
              ((x : t) -> (f x x = True)) -> -- Reflexive proof
              (Reflexive t f)

-- Transitivity: if f x y && f y z then f x z

data Transitive : (t : Type) -> (t -> t -> Bool) -> Type where
  transitive : (f : t -> t -> Bool)                                 ->
               -- Transitive proof
               ((f x y = True) -> (f y z = True) -> (f x z = True)) ->
               (Transitive t f)

-- Reflexivity and Transitivity (for convenience)

data RefTrans : (t : Type) -> (t -> t -> Bool) -> Type where
  refTrans : (t : Type)           ->
             (f : t -> t -> Bool) ->
             (Reflexive t f)      ->
             (Transitive t f)     ->
             (RefTrans t f)

-- <= is reflexive and transitive (proof ommitted)
lert : RefTrans Int le
lert = ?lertp

----------------------------------------------------
-- Force comparisons to be reflexive & transitive --
----------------------------------------------------

data WithRT : Nat              ->    -- Length
              (t : Type)       ->    -- Element type
              (t -> t -> Bool) ->    -- Comparison function
              Type             where

  wrtNil  : (f : t -> t -> Bool) ->  -- Comparison function
            (RefTrans t f)       ->  -- RefTrans proof
            (WithRT 0 t f)           -- Empty list

  wrtCons : (x : t)            ->    -- Element
            (WithRT    n  t f) ->    -- List
            (WithRT (S n) t f)       -- Increment length

-- Still doesn't affect our element order (proofs ommitted)

sort6 : (f : (t -> t -> Bool)) ->
        (l : List t)           ->
        (WithRT (length l) t f)
sort6 f []      = wrtNil  f ?qs6
sort6 f (x::xs) = wrtCons x (sort6 f xs)

--------------------------
-- A truly sorted list! --
--------------------------

data Sorted :  Nat                 ->  -- Length
              (t : Type)           ->  -- Element type
              (Maybe t)            ->  -- Smallest element (Nothing for [])
              (f : t -> t -> Bool) ->  -- Comparison function
              (RefTrans t f)       ->  -- RefTrans proof
               Type            where

  sNil  : (f : t -> t -> Bool)  ->     -- Comparison function
          (p : RefTrans t f)    ->     -- RefTrans proof
          (Sorted 0 t Nothing f p)     -- Empty list

  sOne  : (x : t)                ->    -- Element "x"
          (f : t -> t -> Bool)   ->    -- Comparison
          (p : RefTrans t f)     ->    -- RefTrans proof
          (Sorted 1 t (Just x) f p)    -- "x" is smallest (no other values)

  sMany : (x : t)                          ->  -- Element type
          (Sorted (S n) t (Just y) f p)    ->  -- List; "y" is smallest
          (f x y = True)                   ->  -- x is smaller than y
          (Sorted (S (S n)) t (Just x) f p)    -- n++, x is smallest

-- Sorted list -> List. Drops extra information.
sToList : (Sorted n t x f p) -> (List t)
sToList (sNil  _ _)    = []
sToList (sOne  x _ _)  = [x]
sToList (sMany x xs _) = x :: (sToList xs)

-- Smallest value in a List
rtMin : (f : t -> t -> Bool) ->
        (RefTrans t f)       ->
        (List t)             ->
        (Maybe t)
rtMin _ _ []         = Nothing
rtMin f _ (x::[])    = Just x
rtMin f p (x::y::zs) = rtMin f p ((if f x y then x else y) :: zs)  

-- Length of a Sorted list
sLength : (Sorted n t x f p) -> Nat
sLength (sNil  _ _)      = 0
sLength (sOne  _ _ _)    = 1
sLength (sMany _ s _) = S (sLength s)

-- Pick smallest value for a length
sRMin : Nat -> t -> Maybe t
sRMin Z _ = Nothing
sRMin _ x = Just x

-- Sorted list of [x, x, x, x, ...]
rtReplicate : (n : Nat)            ->
              (x : t)              ->
              (f : t -> t -> Bool) ->
              (p : RefTrans t f)   ->
              (Sorted n t (sRMin n x) f p)
rtReplicate  Z        x f p = sNil  f p
rtReplicate (S Z)     x f p = sOne  x f p
rtReplicate (S (S n)) x f p = sMany x (rtReplicate (S n) x f p) ?sR

-- Our sort function *must* give a Sorted list of the same length
sort7 : (f : t -> t -> Bool) ->  -- Comparison function
        (p : RefTrans t f)   ->  -- RefTrans proof
        (l : List t)         ->  -- Input list
        (Sorted (length l) t (rtMin f p l) f p)

-- We can find the smallest value and replicate it!
sort7 f p []         = sNil f p
sort7 f p (x::[])    = sOne x f p
sort7 f p (x::y::zs) with (rtMin f p (x::y::zs))
  | Just m  = rtReplicate (S (S (length (zs)))) m f p

---------------------------------------------------------------
-- Sorted isn't enough; output must be permutation of input! --
---------------------------------------------------------------

-- Disambiguate List/Vect
lCons : a -> List a -> List a
lCons = (::)

-- Proof that an element is in a List
data In : t      ->  -- Element
          List t ->  -- List
          Type   where

  -- "x" is in "x::xs" for all "xs"
  isHead : (x : t) ->
           (In x (lCons x xs))

  -- If "x" is in "l", "x" is in "y::l" for all "y"
  inTail : (x : t)  ->
           (In x l) ->
           (In x (lCons y l))

-- If every input element is in the output, it's a permutation 
data Permutation : (List t) -> (List t) -> Type where
  isPerm : (l1 : List t)                       ->  -- List1
           (l2 : List t)                       ->  -- List2
           ((x : t) -> (In x l1) -> (In x l2)) ->  -- Proof
           (Permutation l1 l2)

sBiggest : (Maybe t) ->
           (Maybe t) ->
           (t -> t -> Bool) ->
           (Maybe t)
sBiggest Nothing  Nothing  f = Nothing
sBiggest (Just x) Nothing  f = Just x
sBiggest Nothing  (Just x) f = Just x
sBiggest (Just x) (Just y) f = Just (if f x y then x else y)

sort8 : (f : t -> t -> Bool) ->
        (p : RefTrans t f)   ->
        (l : List t)         ->
        (s : Sorted (length l) t (rtMin f p l) f p **
             Permutation (sToList s) l)
sort8 f p []         = (sNil   f p ** ?s8N)
sort8 f p (x::[])    = (sOne x f p ** ?s8O)
sort8 f p (x::y::zs) = ?s8M
