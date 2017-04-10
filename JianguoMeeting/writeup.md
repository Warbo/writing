---
title: Jianguo Meeting Notes
---

## Overview of what we're trying to do ##

 - Take in functions definitions in some language (recursive equations; haskell;
   scheme; etc.)
 - Output equations relating those definitions, using universally-quantified
   variables, checked via random testing. These could be sent to a theorem
   prover afterwards, but we're mostly concerned with the conjectures.

### Example: Peano natural numbers ###

```
Z : ℕ           Note, 'Z' is just a name, representing 0; it's not a variable
S : ℕ → ℕ,      "Successor", i.e. ∀n : ℕ, S(n) : ℕ
```

We can define functions on these, e.g.

```
 plus(Z,    y) = y                            Standard recursive definition of +
 plus(S(x), y) = S(plus(x, y))

times(Z,    y) = Z                            Standard recursive definition of ×
times(S(x), y) = plus(y, times(x, y))
```

We can write equations involving these, e.g.

```
∀x : ℕ, plus(Z, x) = x                          i.e. 0 + x = x
∀x : ℕ, plus(x, Z) = x                          i.e. x + 0 = x
∀x : ℕ, plus(x, x) = times(S(S(Z)), x)          i.e. x + x = 2 × x
∀x : ℕ, ∀y : ℕ, plus(x, y) = plus(y, x)         i.e. x + y = y + x
...
```

We don't want *all* equations; e.g. `plus(Z, Z) = Z`, `plus(Z, plus(Z, Z)) = Z`,
etc. Only "interesting" ones.

### Existing Approach ###

We have a system which will do this (QuickSpec), but it is exhaustive and slow.

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
of work comparing terms which we may consider unrelated. For example, if we give
the system definitions of `plus`, `times` and `parseHTTPHeader`, it will treat
them all as black boxes, despite the fact that `plus` and `times` are very
similar (compare their definitions above).

#### Aside: Generating New Functions ####

Jianguo observed that if we're enumerating terms in the language, won't we
generate new function definitions, in addition to those we're given?

This is interesting. The naive answer is that we won't generate new functions,
since we're only enumerating *function applications*. Our language is a form of
λ-calculus, with a grammar something like this (details vary, e.g. between
SMT-LIB, Haskell, Isabelle, etc.):

```
term := <app> | <func> | <var>

app  := ( <term> ) ( <term> )

func := λ <var> <term>

var  := a | b | c | ...
```

Our input is a set of pairs, each one containing a unique name (e.g. `plus`) and
a `<func>` (e.g. a λ-calculus encoding of Peano addition). The grammar we use to
generate terms is more limited:

```
term := <app> | <var>

app  := ( <term> ) ( <term> )

var  := f1 | f2 | f3 | ... | v1 | v2 | v3 | ...
```

Where the `f`s are the names in our input (e.g. `plus`), and the `v`s are
variable names we add in at the start (3 for each type). Hence we can never
generate new definitions, since we never use the `<func>` rule.

If we think a bit harder, it's actually very easy to end up defining new
functions, if our inputs can *encode* function definitions! It's very easy to
"embed" one functional language inside another, so it's common for APIs to be
written as domain-specific languages (e.g. Parsec, miniKanren, etc.).

As a trivial example, it's well known that untyped λ-calculus can be encoded
using only the S and K functions from combinatory logic:

```
S(x, y, z) = x(z, y(z))

K(x, y) = x
```

If we send these two simple definitions into our conjecture generators, the
term generator will be systematically enumerating all computable functions!

So is this an issue, conceptually or practically? I'd say no in both cases. If
the input domain encodes functions efficiently (i.e. with few symbols, like SK
calculus terms), then we *will* generate (encoded) functions as part of the
search, but that's arguably what we want, since that's what those functions
"do". If the functions don't encode a way to define functions, or don't do so
efficiently, then new functions won't be generated (either because they can't be
expressed, or because the terms would be too big for the search to find,
respectively); which, again, is arguably what we want.

### Proposed Improvements ###

We have two proposed improvements: both may improve speed, but reduce "quality".

Proposal one: split up the input into a number of smaller "buckets", and check
each bucket separately. This introduces a couple of parameters: how many buckets
to use, and how to distribute the definitions between them? As a rule of thumb,
we'll use the square root of the number of definitions as the number of buckets;
we'll distribute inputs uniformly, based on a (SHA256) hash of their names:

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

Proposal two: use the same approach of bucketing, but try to be smart about
which definitions we group together by comparing the definitions themselves
(consider the above example of `plus`, `times` and `parseHTTPHeader`).

We've implemented one particular algorithm to do this (Katya's "recurrent
clustering" algorithm), but there could potentially be many more (e.g. using
models like bag of words, latent semantic analysis, word2vec, etc.).

The two main questions we have are:

 - How do we compare the performance of these systems, in terms of running time?
 - How do we compare the "quality" of the outputs? Limiting searches to separate
   buckets means that we won't find equations involving functions from different
   buckets; how much of a problem is this?

### Benchmark Method ###

We have adapted a benchmark suite designed for testing the capability of theorem
provers, to instead use as the ground truth for this exploration/conjecturing
task.

The suite contains 343 benchmarks; each benchmark contains a single theorem,
e.g. `x × (y + z) = (x × y) + (x × z)`, along with the datatypes and functions
used in that theorem (in this example, a declaration of the type `ℕ` and
definitions of the `+` and `×` functions). Ignoring duplicates, there are 269
function definitions. We can use these as our ground truth in two ways:

 - Each benchmark theorem is "good", in the sense that a human bothered to write
   it down in a formal system and check whether theorem provers can prove it. We
   can assume theorems which *aren't* in the benchmarks are "bad" (and send
   patches to the benchmark suite otherwise!).
 - Since each benchmark contains the definitions it uses, if we only have a
   subset of the definitions we can tell which theorems are still possible. This
   lets us:
    - Draw samples from the definitions, rather than using all of them (which
      would be far too slow).
    - Judge the quality of our bucketing methods, by seeing how many theorems we
      lose due to splitting up their dependencies into separate buckets.

We have a bunch of scripts to work with these benchmarks, to pool together
definitions from multiple benchmarks, sample subsets of the definitions,
translate the functions into various programming languages, find theorems
admitted by a particular subset, etc.

## Comparing Runtimes ##

Our first hypothesis is that separating into buckets will be faster than
searching everything together; although overheads may dominate when the number
of definitions is small.

How can we measure this? We have chosen various sizes (5, 10, 15, etc.) and for
each, we sample 30 subsets of that size from the benchmark definitions (drawn
such that the dependencies of at least one theorem are included, but otherwise
uniformly). We measure how long it takes to search each of these subsets:
completely, bucketing with hashes, and bucketing based on similarity.

Our major question is, how can we compare these runtimes to show if there is any
difference?

For example, here are runtimes (in seconds, on a logarithmic scale) for the
baseline system (QuickSpec), running with sets of size 5:

```{.unwrap pipe="sh | pandoc -f html -t json"}
printf '<img src="data:image/png;base64,'
base64 -w 0 < ./root/quickspec-bars-5.png
printf '" alt="QuickSpec runtimes (seconds) for sample size 5" />'
```

Each bar is for a different sample. The top bars are in the order they were
executed, and show no trend compared to the shuffled bars beneath, indicating
that each samples' run is independent (no effects from caching, etc.). Here are
the same samples, run through our smart bucketing system (MLSpec) instead:

```{.unwrap pipe="sh | pandoc -f html -t json"}
printf '<img src="data:image/png;base64,'
base64 -w 0 < ./root/mlspec-bars-5.png
printf '" alt="QuickSpec runtimes (seconds) for sample size 5" />'
```

How can we compare these in a quantitative way? One observation is that the
times don't seem to be normally distributed; they appear to follow a power law
(many small values, a few large ones).

### Jianguo's Advice ###

Do not try to aggregate these runs together: any attempt to average them will be
dominated by the few large values, and comparing across samples is apples to
oranges.

Instead, calculate the *difference between two systems*, for each individual
sample, known as a paired difference test. If we only have a few samples, we can
use a Wilcoxon signed-rank test; for more than 10 samples with a non-zero
difference, this converges towards a normal distribution, so a standard paired
Z-test can be used instead; since we're running 30 iterations, we can use the
latter. Our null hypothesis is that the average difference is zero.

This is valid even for non-normal data. It's also robust against timeouts:

 - If both systems time out for some input, their difference is zero, so that
   sample gives *less* evidence for a difference between the systems.
 - If one system times out and the other doesn't, the timeout sets a cap on how
   large the difference between them can be, and hence on how much evidence that
   sample can provide for a difference between the systems.
 - If neither system times out, nothing special happens.

Hence the presence of timeouts cannot cause false positives; it just reduces our
confidence in true positives.

We want to compare performance over a range of sample sizes (say, up to 100). It
would be nice to have a graph of the speed difference, say comparing everything
to QuickSpec, with the 95% confidence interval and mean, whose zero crossing is
the point where the overheads become worth it.

Jianguo suggested maybe plotting the p-value/confidence against sample size;
showing how confident we are that a system is faster, rather than giving a
particular speedup factor. This doesn't seem like the nicest visualisation,
since:

 - p-value isn't an immediately obvious, easy to interpret value like
   speedup might be.
 - p-value isn't a proxy for speed: we could be *very* confident that we're
   slightly better.

## Comparing Outputs ##

Existing systems (QuickSpec, HipSpec, IsaCoSy and IsaScheme) compare their
results to theorems from the Isabelle theorem prover's standard library. They
measure:

 - Precision, defined as $\frac{Number of good theorems found}{Number of theorems found}$
 - Recall, defined as $\frac{Number of good theorems found}{Number of good theorems possible}$

We're considering a similar approach, but using our benchmarks as a larger
dataset than the existing ones, which only have about a dozen theorems.

### Jianguo's Advice ###

These definitions of precision and recall are different from those Jianguo is
used to, e.g. in machine learning.

Instead, we might want to come up with a single numeric "score" (e.g. F-score,
or some novel scoring function), then do the following:

 - Define a cutoff value for this score, e.g. 0.8.
 - Rank all results in order of their score.
 - The positives are those with score higher than the cutoff, the negatives are
   those below.
 - The true positives/false negatives are those whose output we consider to be
   good.
 - The false positives/true negatives are those whose output we consider to be
   bad.

Think about possible ways that a result (equation) might get a high score,
despite being subjectively bad. Likewise, think about ways that a good result
might get a bad score.

Personally, I'm not too sure about introducing this approach. We don't want to
reinvent all of the wheels, and the existing precision/recall tables seem like a
reasonable thing to build upon. Jianguo's precision/recall measure is maybe more
suited to something like a classifier.
