---
title: Problems with Dependent Types
author: Chris Warburton
---

# Type Proliferation #

```
data Nat       =  Z    : Nat
               |  S    : Nat     -> Nat

data Fin  n    = fZ    : Fin n
               | fS    : Fin n   -> Fin (S n)

data Lte  n m  = lZ    : Lte n n
               | lS    : Lte n m -> Lte n (S m)

data Elem x xs = here  : Elem x (x::xs)
               | there : Elem x xs -> Elem x (y::xs)
```

Lots of values which all have the same runtime behaviour, but different static types

Functions written for one type of value can't be re-used for another, even though they're the same

Proof Objects

 - Propositional equality

Expression Problem

Solutions

Generic Programming

 - Very complicated types
 - Difficult to come up with

Univalence

 - No algorithm yet

Automated Theorem Proving

 - Get stuck on higher-order things

Tooling

 - IDE support
 - ML4PG
