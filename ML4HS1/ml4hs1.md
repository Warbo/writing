---
title: Machine Learning for Theory Exploration
---

# Introduction

Theory exploration (TE) investigates the consequences of formal definitions, ie. which theorems they induce. It is related to the idea of lemma discoveryFIXME, although TE is open-ended: there is no specific goal, we are not trying to (dis)prove a *particular* theorem. Rather, we are learning the nature and properties of the theory as a whole.

Clearly we must provide *some* guidance to the exploration, to avoid "un-interesting" theorems like $0 = 0$, $1 = 1$, etc. We can denote what is "interesting" by using a classification function $i : Theorem \rightarrow Boolean$. Our exploration problem is then a *function inversion* task:

$$TE(i) := \{ x : Theorem \mid i(x) = True \}$$

Automated function inversion is a common problem in the domains of Artificial Intelligence and Machine Learning. In this paper, we investigate the use of AI and ML techniques for exploring libraries of Haskell code.

# Theory Exploration in Haskell

We choose Haskell as our target, since it has already been studied by the TE systems QuickSpecFIXME and HipSpecFIXME. In turn, these chose Haskell due to the relatively simple semantics of pure functions, and the ability to build on the widely used QuickCheck property checker. Isabelle has also been the target of theory exploration systems, including IsaCoSyFIXME and HipsterFIXME; since Hipster translates Isabelle into Haskell before exploration, Haskell still seems the most suitable target for effective comparisons.

The main problem with these approaches is their use of brute-force search. This has the benefit of being *complete* (all theorems will eventually be found), but limits the scope of what can be discovered in a reasonable time. In particular, the approach scales exponentially in the size of the theorems and factorially in the number of definitions. It can be argued that small theorems are more general, and hence more interesting; but the requirement to manually specify only a few "promising" definitions up-front certainly limits these tools' potential. Indeed, *unexpected* theorems are usually the most interesting of all!

# Reasoning By Analogy

Our approach is a form of *reasoning by analogy*: we take the structure of an existing, interesting theorem and try to construct new theorems with a similar structure in a different domain. In this way, it is not only likely that a theorem will be found (depending on the similarity of the domains), but also that it will be interesting.

Before exploration, every symbol is *clustered* with similar symbols, based on their definitions. During exploration, we pick a known theorem and try substituting its symbols with other members of the same cluster. This produces several candidates, which may be ill-typed. We apply a series of heuristic transformations to fix these types, before attempting to prove them.

# Feature Extraction and Clustering

We cluster all symbol definitions *recurrently*, using a variant of the algorithm in FIXME. This requires an interleaving of feature extraction (conversion of definitions to learnable numbers) and clustering (grouping similar numberings together). The main differences are the removal of APL2-specific constants, the addition of types (following FIXME) and the need to handle cyclic dependencies.

First we produce the dependency graph $D$ of all definitions to be clustered. This is simply the dependency graph of the Haskell modules under consideration, with each module replaced by the dependency graph of its definitions. We use the Glasgow Haskell Compiler (GHC) framework to provide globally unique names across modules.

We initialise a "working list" $W := []$, a lookup table for features $F = \{ \}$ and a set of clusters $C = \{ \}$. We then traverse $D$ in topological order: for each definition $d \in D$, we follow the algorithm **Dependency Order**.

Algorithm **Dependency Order**:

 1) Append $d$ to $W$
 1) If there are any elements $w \in W$ which have dependencies not appearing in $W$ or in $F$, move on to the next definition
 1) Otherwise, perform algorithm **Feature Extraction** on each $w \in W$ to obtain $f_w$
 1) Set $F := F union \{ (w, f_w) \}$
 1) After all elements of $W$ have been handled, set $W := []$
 1) Cluster $F$ to obtain a new value of $C$
 1) Move on to the next definition

Algorithm **Feature Extraction**:

Replace all symbols $s$ occuring in the given definition $d$, based on the following rules:

 - If $s$ is a named argument of $d$, replace $s$ with the argument's position ($1$, $2$, etc.)
 - If $s \in C_n$, for some $C_n \in C$, replace $s$ with $n$
 - If $s$ appears at index $n$ in $W$ (starting from $1$), replace $s$ with $-1 \times n$
 - Convert the tree structure of $d$ to a matrix $M$, such that $M_{ij}$ is the $i$th

Algorithm **Cluster**:

 1)

Algorithm **Matrix**

 1) If the definition $d$ only contains a single symbol $s$, return the matrix $N_v(s) N_t(s) 0$

# Future Work

Previous comparisonsFIXME of particular clustering methods, including k nearest neighbours, FIXME, found no significant difference in performance between these approaches. However, there are still many arbitrary choices to be made before and after clustering. Of course, there are also many other machine learning techniques besides clustering which may be applicable to the problem of efficient theory exploration.

Our approach has many parameters, including truncation size, cluster granularity and FIXME, which we choose in an ad-hoc empirical way. Many of these parameters determine a tradeoff between performance and accuracy, which makes them potential candidates for the *parameterless* approach of FIXME.

Our approach to feature extraction is based on successful applications in CoqFIXME and ACL2FIXME, but there is a lot of freedom for experimentation. In particular it would be interesting to compare our highly-informed approach to a purely learned alternative like auto-encoding. The key requirement is to handle the nested structure of definitions, which has been attempted by *backpropagation through structure*FIXME and recurrent neural networksFIXME.

Another potential for improvement is to "tie the knot" and have the theorems we find influence our notion of similarity. For example, our existing feature extraction method considers `a + b`{.haskell} and `b + a`{.haskell} to be different, which will separate their features slightly. If our theory exploration discovers commutativity of addition `x + y = y + x`{.haskell}, we could use this to normalise all occurances of addition, and hence bring these features closer together.

# References
