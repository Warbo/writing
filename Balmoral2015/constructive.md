# Part 1: Decisions #

# Decision Problem #

Decision procedure: for all A, prove A or prove ~A

# Goedel #

Incompleteness Theorem

There is no decision procedure

Distinguish between TRUE and PROVABLE

# Constructive Logic #

Brouwer's Intuitionism

Formalised by Heyting

"True" = "provable"

Proof requires evidence

# Constructive Logic: Simple Operators #

Proof of P

Proof of P AND Q

Proof of P OR Q

# Constructive Logic: Implication #

Proof of P IMPLIES Q

 - Algorithm/function/etc. MUST BE TOTAL

Proof of NOT P

 - Special case of implication

# Constructive Logic: Quantifiers #

Proof of FOR ALL x, P(x)

 - Implication is a special case
    - Hence NOT P is a really special case

Proof of THERE EXISTS AN x, SUCH THAT P(x)

 - AND is a special case

Note: This is dependent type theory!

# Constructive Logic: Excluded Middle (OR) #

FOR ALL P, P OR NOT P

Matches the type of the Decision Problem

Goedel showed it can't be done!

Consistent, but not provable. Is it "true"?

# Constructive Logic: Lack of evidence (EXISTS) #

N : Nat
N = if P = NP then 0 else 1

THERE EXISTS x : Nat, SUCH THAT N + x = 2

Clearly true, but we can't construct evidence without knowing if P = NP!

# Part 2: Classical Time Travel #

# Classical Axioms #

Excluded Middle:

 - FOR ALL P, P OR ~P

Double Negation Elimination:

 - ~(~ P) -> P

Peirce's Law

 - ((P -> Q) -> P) -> P

 - Try to get ((P -> Q) -> X) -> P

# Classical Algorithms: Excluded Middle #

LEM P : P + (P -> False)

 - Permits a function call which doesn't return
 - Instead, jumps to a different location
 - Control flow!

# Excluded Middle: Time Travel Interpretation #

When LEM P is called:

 - Switch on your time machine
    - If a proof of P emerges, return it
    - If not, return a function f : P -> False
    - If f is ever called with a proof of P, it passes that proof into the time machine

# Classical Algorithms: Double Negation Elimination #

DNE : ((P -> False) -> False) -> P

call-by-name CPS

# Classical Algorithms: Peirce's Law #

PL P : FOR ALL Q. ((P -> Q) -> P) -> P

call/cc

# Curry Howard #

Application to many more logics

 - Linear (single-use resources)
 - Modal (staged)

# References #
