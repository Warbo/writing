module QuickSpecExample where

import Numeric.Natural
import Test.QuickSpec
{-
i2N :: Int -> Natural
i2N = fromInteger . toInteger

sigma = [blind0 "()"      (),
         blind0 "Z"       ([] :: [()]),
         blind1 "length"  ((i2N . length) :: [()] -> Natural),
         blind2 "++"      ((++) :: [()] -> [()] -> [()]),
         --blind1 "reverse" (reverse :: [()] -> [()]),
         blind2 "s"       ((:) :: () -> [()] -> [()]),
         blind0 "F"       False,
         blind0 "T"       True,
         blind0 "0"       (0 :: Natural),
         blind1 "S"       ((+ 1) :: Natural -> Natural),
         blind2 "+"       ((+) :: Natural -> Natural -> Natural),
         blind2 "*"       ((*) :: Natural -> Natural -> Natural),

         vars ["b1", "b2", "b3"] True,
         vars ["l1", "l2", "l3"] [()],
         vars ["n1", "n2", "n3"] (0 :: Natural),
         vars ["u1"]             (),

         observer1 ((i2N . length) :: [()] -> Natural),
         observer1 (id :: () -> ()),
         observer1 ((`mod` 10) :: Natural -> Natural),
         observer1 (id :: Bool -> Bool)]
-}

nat = [fun0 "True"  (True  :: Bool),
       fun0 "False" (False :: Bool),
       fun0 "Z"     (0     :: Natural),
       fun1 "S"     ((1+)  :: Natural -> Natural),
       fun1 "not"   (not   :: Bool    -> Bool),
       fun1 "odd"   (odd   :: Natural -> Bool),
       fun1 "even"  (even  :: Natural -> Bool),

       vars ["x", "y", "z"] (0    :: Natural),
       vars ["a", "b", "c"] (True :: Bool)]
