---
title: Expression Problems with Dependent Types
author: Chris Warburton
---

# A Couple of Interesting Types #

<!-- Take our examples from exercises.agda to ensure they're up-to-date -->

<div style="display: none">

```{pipe="cat > getBetween"}
#!/bin/sh
# Returns stdin between lines matching $1 and $2
(grep -A 100 "$1" || (echo "'$1' NOT FOUND"; exit 1)) | tail -n +2 | \
(grep -B 100 "$2" || (echo "'$2' NOT FOUND"; exit 1)) | head -n -1
```

```{pipe="cat > getEx"}
#!/bin/sh
# Look for a specific example in exercises.agda
./getBetween "^-- START EX $1" "^-- END EX $1" < root/exercises.agda
```

```{.unwrap pipe="sh"}
# Type-check our Agda
agda -c root/exercises.agda > /dev/stderr || exit 1
chmod +x get*
```

</div>

(Heterogeneous) Equality:

```{.haskell pipe="./getEx Eq_def"}
```

Dependent Pairs:

```{.haskell pipe="./getEx DPair_def"}
```

We'll use these later...

# Guess the Type #

What does the following type represent?

```{.haskell pipe="./getEx T_def"}
```

It contains values like:

```{.haskell pipe="./getEx T_vals"}
```

# `T n m`{.haskell} = `n ≤ m`{.haskell} #

`p : LTE n m`{.haskell} is a proof of `n`{.haskell} $\leq$ `m`{.haskell}:

```{.haskell pipe="./getEx LTE_def"}
```

It contains values like:

```{.haskell pipe="./getEx LTE_vals"}
```

# `LTE n m`{.haskell} is Transitive #

```{.haskell pipe="./getEx LTE_trans"}
```

# `lteTrans`{.haskell} looks familiar... #

```{.haskell pipe="./getEx Nat_def"}
```

The values and algorithms are identical!

# `LTE n m`{.haskell} $\subset$ ℕ #

`v : LTE n m`{.haskell} is a ℕ, such that `n`{.haskell} $+$ `v`{.haskell} $=$ `m`{.haskell}

It's the *difference* between `n`{.haskell} and `m`{.haskell}

```{.haskell pipe="./getEx LTE_prop"}
```

To type-check, we needed to convert `LTE n m`{.haskell} to `Nat`{.haskell}...

# `LTE n m`{.haskell} #

Why don't we just use `Nat`{.haskell}?

We'd have to include proof of our desired property too:

```{.haskell pipe="./getEx LTE2_def"}
```

This ensures `LTE2 n m`{.haskell} is equivalent to `LTE n m`{.haskell}

# `LTE2 n m`{.haskell} #

We're now using `Nat`{.haskell}, but we have to prove `lte2Prop`{.haskell} for *each* value separately!

```{.haskell pipe="./getEx LTE2_vals"}
```

Thankfully Agda's proof search can handle these simple cases.

# Currying #

Having to extract the first element of a `LTE2 n m`{.haskell} isn't much different than having to `l2N`{.haskell} a `LTE n m`{.haskell}.

Instead, we can keep the `Nat`{.haskell} and `lte2Prop`{.haskell} proofs separate and curry any function which needs both:

```{.haskell pipe="./getEx Curry_def"}
```

# Example #

```{.haskell pipe="./getEx Curry_one"}
```

# What Have We Achieved? #

 - Seen a few dependent type "design patterns": `Eq`{.haskell}, `DPair`{.haskell}, proof objects...
 - Found relationships between bespoke types to off-the-shelf ones
 - Separated proof obligations from algorithm implementations
 - Made our obligations more amenable to automated proof search

# Conclusion #

 - We're always stuck with the expression problem (verbs vs. nouns)
 - Dependent types add a new dimension: properties
 - Carrying properties in types ('correct by construction') is more elegant
 - Separating properties gives us more flexibility
    - Possibility to automate, without altering our algorithms
    - No property is more privileged than another (eg. functions vs methods)
 - Everything's still up in the air!
