## Improving Haskell Theory Exploration ##

--------------------------
      Chris Warburton

 cmwarburton@dundee.ac.uk

        2015-12-17

 <img src="dundee_logo.png" />
--------------------------

## Haskell ##

``` haskell
-- Lazy
ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t e = t
ifThenElse False t e = e

-- Pure
max1 :: (Ord a) => a -> a -> a
max1 x y = ifThenElse (x > y) x y

max2 :: (Ord a) => a -> a -> IO a
max2 x y = callCommand "rm -rf /" >> return (max1 x y)

-- Equational
{-# RULES
  "double/shift" forall x.  x * 2 = x << 1
  "shift/double" forall x.  2 * x = x << 1
  #-}

cast :: (a ~ b) => a -> b
cast x = x
```

<style type="text/css">
.haskell {
  font-size: x-large;
}
</style>

## Goal: Understanding Code ##

 - Unit testing: Self-contained
    - `factorial 3 == 6`
 - Property checking: Generate and test values
    - `f n = factorial n <= factorial (n+1)`
 - Theorem proving: Derive from the code
    - $\forall$ `n. factorial n <= factorial (n+1)`
 - Theory exploration: generate and prove properties
    - High confidence for low cost

## Existing Methods ##

Enumerate type-correct properties for all terms (HipSpec):

 - Assume all terms of a type are equal
 - Use QuickCheck to disprove most
 - Try to prove the remainder

. . .

 - Scales poorly
 - Can we choose more intelligently?

## Relevance Filtering ##

 - Used for automated theorem proving.
 - Only search those terms which are "relevant" to the goal
 - Use machine learning to find relevance (e.g. naive bayes)

. . .

 - Theory exploration has no "goal" term
 - We need relevance of all terms to all other terms
 - Use *clustering* instead

## Recurrent Clustering ##

 - Convert tree structure to feature vector, preserving alignment
 - Convert syntax to hard-coded features
 - Cluster dependencies, use their cluster number as reference's feature
    - References to similar expressions get similar features
    - Recursion gets a dummy value

```{pipe="cat > dc.dit"}
                 +------+-----+    +---+---+
     App         |App   |     |    |114|  0|
    /   \        +------+-----+    +---+---+    +----+--+----+----+----+---
  Var    Var  -> |Var   |Var  | -> |112|112| -> |114 |0 |112 |112 |110 |...
   /      \      +------+-----+    +---+---+    +----+--+----+----+----+---
Global  Local    |Global|Local|    |110|109|
   /      \      +------+-----+    +---+---+
  map     xs     |"map" |"xs" |    |304|203|
                 +------+-----+    +---+---+
```

```{.unwrap pipe="sh | pandoc -f html -t json"}
ditaa -E dc.dit dc.png > /dev/null
DATA=$(base64 -w 0 < dc.png)
echo "<img src='data:image/png;base64,$DATA' alt='DC' />"
```

## ML4HS Framework ##

 - Fetches Haskell code from Hackage
 - Compiles with a plugin to extract ASTs
 - Sorts ASTs, and performs recurrent clustering
 - Generates and runs QuickSpec signatures

. . .

 - Still to do
    - Data generators
    - Evaluation (no ground truth)

## Future ##

 - Data generators:
    - Make them generically
    - Try alternatives, e.g. LazySmallCheck for conditionals
 - *Interestingness* of properties
    - Many measures proposed
    - Many search algorithms/approaches to try

## Thank You ##

##  ##

<img src="./Gantt.png" width="100%" />
