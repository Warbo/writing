module Foo where
{-
data Foo a = Foo a

class Bar a

instance Foo a => Bar (Foo a)
-}
