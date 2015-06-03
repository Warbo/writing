---
title: "Constructive vs Classical"
author: Chris Warburton
---

# DISCLAIMER #

To prevent confusion, I will *not* be using *any* "Boolean values", as found in common programming languages.

When I say 'true', I mean the every day usage of the word.

 - If you insist on a formal definition, choose any you like (eg. Tarski's)

When I say '`True`', I mean a statement which is trivially true.

When I say '`False`', I mean a statement which is not true.

When I say '`true`', I mean the (trivial) proof of `True`.

# Part 1 #

**Evidence vs Argument**

# "Classical" Logic #

Around since Ancient Greece

Opposed to *rhetoric* (informal argument)

 - Classical logic requires *proof* (formal argument)

Mechanised by Frege, Russell, Hilbert, etc. in 19th & 20th centuries as part of their set theoretic foundations

Includes the *Law of the Excluded Middle* (LEM): `∀P. P ∨ ¬P`

# Classical Logic: LEM → DNE #

LEM implies *double-negation elimination*: ∀P. ¬(¬P) → P

Proof Sketch:

<div style="font-size: 0.5em;">

    1) ∀P. P ∨ ¬P                                    LEM
    2) ∀P. ¬(¬P) → P ∨ ¬P                            Weaken (1) with ¬(¬P)
    3) ∀P. ¬(¬P) → ¬(¬P)                             Identity
    4) (∀P. ¬(¬P) → (P ∨ ¬P)) ∧ (∀P. ¬(¬P) → ¬(¬P))  Introduce ∧ with (2) and (3)
    5) ∀P. (¬(¬P) → (P ∨ ¬P)) ∧ (¬(¬P) → ¬(¬P))      Distribute ∧∀ in (4)
    6) ∀P. ¬(¬P) → (P ∨ ¬P) ∧ ¬(¬P)                  Distribute ∧→ in (5)
    7) ∀P. ¬(¬P) → (P ∧ ¬(¬P)) ∨ (¬P ∧ ¬(¬P))        Distribute ∧∨ in (6)
    8) ∀P. ¬(¬P) → (P ∧ ¬(¬P))                       Consistency of ¬P in (5)
    9) ∀P. ¬(¬P) → P                                 Eliminate ∧

</div>

Rules/axioms used:

<div style="font-size: 0.5em;">

    LEM)             ∀A.     A ∨ ¬A
    Weaken)          ∀A B.   A → B → A
    Identity)        ∀A.     A → A
    Distribute ∧∨)   ∀A B C. (A ∨ B) ∧ C → (A ∧ C) ∨ (B ∧ C)
    Consistency)     ∀A.     ¬(A ∧ ¬A)
    Introduce ∧)     ∀A B C. A → B → A ∧ B
    Distribute ∧→)   ∀A B C. ((A → B) ∧ (A → C)) → A → (B ∧ C)
    Distribute ∧∀)   ∀A B C. ((∀A. B) ∨ (∀A. C)) → (∀A. B ∧ C)
    Eliminate ∧)     ∀A B.   (A ∧ B) → A

</div>

# Classical Logic: Refutation & Resolution #

*Resolution* is a procedure for proving statements in classical logic

To prove the statement `P`:

 - Assume `¬P` (we "refute `P`")
 - Combine pairs of statements until we prove `False` (if we run out, halt)
 - We've reached a contradiction, our assumption must be false, ie. `¬(¬P)`
 - Use double-negation elimination to prove `P`

Widely used in Automated Theorem Provers (E, Vampire, SPASS, ...)

# Resolution: Example 1 #

Prove `1 < 2` using resolution:

<div style="font-size: 0.65em;">

    1) ¬(1 < 2) → ....               Refute 1 < 2 and see what we get
    2) ¬(1 < 2) → 1 ≥ 2              By relationship between < and ≥
    3) ¬(1 < 2) → 0 ≥ 1              Subtract 1 from both sides
    4) ¬(1 < 2) → (0 = 1) ∨ (0 > 1)  By relationship between ≥, = and >
    5) ¬(1 < 2) → False ∨ (0 > 1)    Different constants aren't equal
    6) ¬(1 < 2) → 0 > 1              Eliminate impossible case
    7) ¬(1 < 2) → False              0 is not greater than any Nat
    8) ¬(¬(1 < 2))                   From (7) by contradiction
    9) 1 < 2                         From (8) by double negation elimination

</div>

Note: we never saw evidence that `1 < 2`, only that `¬(¬(1 < 2))`

# Resolution: Example 2 #

Prove that `length(nil)` is well-typed, ie. `∃T. HasType(T, length(nil))`

<div style="font-size: 0.5em;">

    1) ¬∃T. HasType(T, length(nil)) → ....
    2) ¬∃T. HasType(T, length(nil)) → ¬∃T. HasType(T, 0)
    3) ¬∃T. HasType(T, length(nil)) → ¬∃T. HasType(T, Elem(0, "abc"))
    4) ¬∃T. HasType(T, length(nil)) → ¬∃T. HasType(T, 'a')
    5) ¬∃T. HasType(T, length(nil)) → (¬∃T. HasType(T, 'a')) ∧ HasType(Char, 'a')
    6) ¬∃T. HasType(T, length(nil)) → (¬∃T. HasType(T, 'a')) ∧ (∃T. HasType(T, 'a'))
    7) ¬∃T. HasType(T, length(nil)) → False
    8) ¬(¬∃T. HasType(T, length(nil)))
    9) ∃T. HasType(T, length(nil))

</div>

We've proven that `length(nil)` has a type, but we don't know what it is!

Fine for correctness, but useless if we need to select a type class instance.

# Constructive Logic #

*Constructive* proofs require *evidence*

Brouwer's *intuitionistic logic* was the first serious effort

 - Mathematics describes mental constructs; if they cannot be constructed, then they cannot exist!

Corresponds remarkably to total functional programming!

 - Programming describes computatable values; if they cannot be computed, then they cannot exist!

# Constructive Logic: Curry Howard #

The lowercase variables represent our *evidence*

Logic             Programming
-----------       -----------------
Statement `P`     Type `P`
Proof `p` of `P`  Value `p : P`
`P ∧ Q`           Pair type `P × Q`
`P ∨ Q`           Sum type `P + Q`
`P → Q`           Function type `P -> Q`
`¬P`              Function type `P -> False`
`∀p∈P. Q(p)`      Dependent function type `(p : P) -> Q(p)`
`∃p∈P. Q(p)`      Dependent pair type `{p : P | Q(p)}`

# Constructive Logic: Curry Howard #

We can remove some special cases:

Logic             Programming
-----------       -----------------
Statement `P`     Value `P : Set`
Proof `p` of `P`  Value `p : P`
`P ∨ Q`           Sum type `P + Q`
`∀p∈P. Q(p)`      Dependent function type `(p : P) -> Q(p)`
`∃p∈P. Q(p)`      Dependent pair type `{p : P | Q(p)}`

# Constructive Logic: LEM #

If we interpret LEM from a constructive perspective:

    LEM : (P : Set) -> P + (P -> False)

LEM is a *total function* which takes an argument `P` and provides either evidence of `P` or evidence of `¬P`

Such functions are known as *decision procedures*, and LEM is a solution to Hilbert's *decision problem*

Goedel (and later Turing) showed that this problem is *undecidable*: hence there is no total function `LEM`!

# Constructive Logic: LEM #

Without LEM, we cannot prove DNE, hence proving ¬(¬P) by resolution does not prove P! :(

However, all constructive proofs will provide evidence! :)

# Part 2 #

**Classical Time Travel**

# Interpreting Classical Axioms #

If we add LEM to a constructive logic as an axiom, we remain consistent.

If it's not a (total) function, then what are we adding to our language?

# Computational LEM #

`LEM : (P : Set) -> P + (P -> False)`

Given a `P`, `LEM` must return either a `P` or a `P -> False`

 - We *cannot* return a `P`, since we don't have one for all `P` (eg. `False`)
 - We *cannot* return a function `f : P -> False`, since `P` might be true!

# Computational LEM #

We cannot distinguish true `P`s from false ones, if all we're given is `P` itself. We need more information.

If we return `f : P -> False`, we can accept proofs that `P` is true, and hence tell them apart. But by then it's too late, we've already returned `¬P`!

LEM gives us a *time machine*, which we can use like this:

 - When `LEM(P)` is called, switch on the time machine
 - If a proof of `P` emerges from the machine, return it
 - Otherwise, return a function `P -> False`
    - If anyone ever calls the function with a `P`, throw it into the time machine!

LEM is a form of *control flow*, similar to *delimited continuations*!

# Computational DNE #

`DNE : ((P -> False) -> False) -> P`

How can we return a proof of `P`, if all we have are functions?

Our argument function `f : (P -> False) -> False` is claiming to prove `False`, which should be impossible.

The only way it could prove `False` is by calling its argument `g : P -> False`, which requires a proof `p : P`.

We can use call-by-name to prevent these functions being called, then implement a rewrite rule:

    DNE : ((P -> False) -> False) -> P
    DNE (\g -> g p) = p

# Computational Pierce's Law #

Peirce's Law is an alternative to LEM and DNE, which shares some similarities:

    PL : ((P -> Q) -> P) -> P

Just like LEM, PL seems to require proving arbitrary statements (in this case `Q`)

Just like DNE, PL turns functions-of-functions into a proof of `P`


# Computational Pierce's Law #

`PL` must be applied to some function `k` in order to work:

    PL : ((P -> Q) -> P) -> P

    f : (P -> Q) -> P

    PL f : P

# Computational Pierce's Law #

`f` must also be applied to some function `k` in order to work:

    f : (P -> Q) -> P

    k : P -> Q

    f k : P

The function `k` is generated inside `PL` and uses a time-machine just like `LEM`!

When `k` is called with `p : P`, it sends `p` back to the invocation of `PL f`, where it is returned.

Pierce's Law corresponds exactly to Scheme's `call/cc`!

# Conclusions: Classical vs Constructive #

Classical logic can perform "time travel"

 - Classical proofs can stop, rewind, then take a different branch
 - Allows 'making choices' like `A ∨ B` and `∃P. Q` without knowing which choice was taken
 - Very useful for implementing efficient Automated Theorem Provers
 - Not very useful when we need to know the choice, eg. to look up a typeclass

Constructive logic always provides the evidence we need

 - Proofs are more useful, but harder to find

# Conclusions: Curry-Howard #

Programs and proofs are related.

 - Some are straightforward (functional programming vs intuitonistic logic)
 - Some are obscure (classical logic vs `shift/reset` and `call/cc` control flow)
 - Many more relationships:
    - Linear logic/linear types
    - Modal logic/staged computation
    - Temporal logic/FRP
    - ...
