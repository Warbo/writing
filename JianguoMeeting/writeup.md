---
title: Jianguo Meeting Notes
---

Overview of what we're trying to do:

 - Take in functions definitions in some language (recursive equations; haskell;
   scheme; etc.)
 - Output equations relating those definitions, using universally-quantified
   variables, checked via random testing. These could be sent to a theorem
   prover afterwards, but we're mostly concerned with the conjectures.

Example: Peano natural numbers:

```
Z : ℕ           Note, 'Z' is just a name, representing 0; it's not a variable
S : ℕ → ℕ,      "Successor", i.e. ∀n : ℕ, S(n) : ℕ
```

We can define functions on these, e.g.
```
 plus(Z,    y) = y                            Standard recursive definition of +
 plus(S(n), y) = S(plus(x, y))

times(Z,    y) = Z                            Standard recursive definition of ×
times(S(x), y) = plus(y, times(x, y))
```

We can write equations involving these, e.g.

```
∀x : ℕ, plus(Z, x) = x                          0 + x = x
∀x : ℕ, plus(x, Z) = x                          x + 0 = x
∀x : ℕ, plus(x, x) = times(S(S(Z)), x)          x + x = 2 × x
∀x : ℕ, ∀y : ℕ, plus(x, y) = plus(y, x)         x + y = y + x
...
```

We don't want *all* equations; e.g. `plus(Z, Z) = Z`, `plus(Z, plus(Z, Z)) = Z`,
etc. Only "interesting" ones.

We have a system which will do this (QuickSpec), but it is exhaustive and slow.
We have two proposed improvements: both may improve speed, but reduce "quality".

Existing approach (QuickSpec):

```{.unwrap pipe="goat /dev/stdin | pandoc -t json"}
Input function
definitions                                 Output equations

+--------+                                  +-----+
|f(x) = ⋯|                                  |a = b|
+--------+     .----------------------.     +-----+
|g(x) = ⋯|---->|Check all combinations|---->|c = d|
+--------+     '----------------------'     +-----+
|   ⋯    |                                  |  ⋯  |
```

Given definitions for functions `f`, `g`, `h`, etc., QuickSpec will add some
variables, say `x`, `y` and `z`, then enumerate all terms in a simple grammar
of function application involving these functions and variables; stopping when
it reaches a predetermined level of nesting (3 by default). For the above
functions, terms would include `f`, `g(x, f(y))`, `h(h(x), f(h))`, etc.
(depending on the input and output types of `f`, `g` and `h`).

We then pick a random value for the variables (`x`, `y` and `z`), substitute
these values into the terms, run them as programs and compare the results. For
any which gave equal results, we pick new random values for the variables and
compare them again, and so on. If there are any terms which gave equal results
across 1000 random substitutions, we output a conjecture that the terms are
equal.

This approach is exhaustive, since it produces every possible term. That means
it's guaranteed to find an equation if it exists; but it will also perform a lot
of work comparing terms which we may consider unrelated.

Proposal one: split up the input into a number of smaller "buckets", and check
each bucket separately. As a rule of thumb we'll choose a number of buckets
that's the square root of the number of function definitions. To distribute
inputs uniformly, we assign them to buckets using a generic hash function
(SHA256):

```{.unwrap pipe="goat /dev/stdin | pandoc -t json"}
Input                                                                   Combined
definitions      Buckets                                  Equations     Output
                 +--------+                               +-----+
                 |f(x) = ⋯|                               |a = b|
                 +--------+   .----------------------.    +-----+.
                 |p(x) = ⋯|-->|Check all combinations|--->|c = d| \      +-----+
+--------+    .->+--------+   '----------------------'    '-----'  \     |a = b|
|f(x) = ⋯|   /                                                      \    +-----+
+--------+  /    +--------+   .----------------------.    .-----.    \   |c = d|
|g(x) = ⋯|-+---->|h(x) = ⋯|-->|Check all combinations|--->|p = q|-----+->+-----+
+--------+  \    '--------'   '----------------------'    +-----+    /   |p = q|
|   ⋯    |   \                                            |w = z|   /    +-----+
              '->.--------.                               '-----'  /     |  ⋯  |
                 |g(x) = ⋯|                                       /
                 +--------+   .----------------------.    .-----./
                 |q(x) = ⋯|-->|Check all combinations|--->|x = y|
                 +--------+   '----------------------'    +-----+
                                           ⋯
```

Proposal two: use the same approach of bucketing, but try to be smarter about
which functions we put together by comparing their definitions. We've
implemented one particular algorithm to do this (Katya's "recurrent clustering"
algorithm), but there could potentially be many more (e.g. using models like bag
of words, latent semantic analysis, word2vec, etc.).

The two main questions we have are:

 - How do we compare the performance of these proposals, in terms of running
   time?
 - How do we compare the "quality" of the outputs? Since we won't generate terms
   involving functions from separate buckets, or compare terms across buckets,
   we're ruling out a large number of possible equations. How much of a problem
   is this?
