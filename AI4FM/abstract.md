---
title: Scaling Automated Theory Exploration
author: Chris Warburton
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
header-includes:
    - \usepackage[T1]{fontenc}
    - \usepackage{upquote}
---

# Abstract #

In this paper we investigate the **theory exploration** (TE) paradigm for computer-assisted Mathematics and identify limitations and improvements of current approaches. Unlike the theorem-proving paradigm, which requires user-provided conjectures, TE performs an open-ended search for theorems satisfying given criteria. We see promise in TE for identifying new abstractions and connections in libraries of software and proofs, but realising this potential requires more scalable algorithms than presently used.

# Introduction #

The *theory exploration* (TE) paradigm provides software support for traditional Mathematical workflows; namely, deriving "interesting" consequences from formal definitions [@RISC1482]. Early implementations like <span style="font-variant:small-caps;">Theorema</span> [@buchberger2000theory] emphasised interactivity, in a similar way to computer algebra systems like <span style="font-variant:small-caps;">Mathematica</span> (in which <span style="font-variant:small-caps;">Theorema</span> is implemented) or interactive theorem provers. Subsequent systems have investigated *automated* theory exploration, for tasks such as lemma discovery [@Hipster].

By removing user interaction, automated TE systems require an algorithm for deciding whether a theorem is "interesting". In existing systems, this is intimately connected to the choice of search algorithm, to ensure tractability. For example, <span style="font-variant:small-caps;">IsaCoSy</span> [@johansson2009isacosy] discovers equations, which are defined as "interesting" if they cannot be simplified using previously discovered equations. The intuition for such criteria is to avoid special cases of known theorems, such as $0 + 0 = 0$, $0 + 1 = 1$, etc. when we already know $\forall x. 0 + x = x$. To work effectively, this requires general forms to be found *before* special cases.

TE is a "bottom-up" process: new theorems are derived from given knowledge and previous theorems. In particular, there is no special "goal" theorem(s) as found in interactive theorem proving; all we have is our (proxy) "interesting" criterion, and the definitions of our theory. This makes theory exploration a *combinatorial optimisation* problem, which is well studied in Artificial Intelligence and Machine Learning. Existing TE systems rely on complete, brute-force search techniques which do not scale to theories of a significant size; these could be replaced by a variety of faster, approximate algorithms, eg. those surveyed in [@blum2011hybrid].

Whilst efficient on a small scale, where we expect the chosen inputs to be related, we cannot expect an effective output criterion to coincide so readily with search algorithm and output criterion to be effective for large inputs containing many irrelevant connections. umbers of also consider data mining approaches, which infer general rules *after* enumerating some number of special cases. A variety of "interestingness" measures are used in domains such as data mining [@geng2006interestingness], which may be adapted to a TE setting. These include objective measures, eg. based on information theory, and subjective measures which ask for the user's opinion. We can avoid asking users directly, by treating existing proof libraries and test suites as representative examples of what is interesting, and hence construct an oracle; such oracles have already been used for precision-recall experiments to evaluate the performance of <span style="font-variant:small-caps;">HipSpec</span> [@claessen2013automating].

# Tackling Complexity #

Even with a slow search algorithm, we can use a divide and conquor approach to limit the number of allowed combinations, either by using stricter types to prevent composition, or by partitioning the theory into small independently-searched sub-theories. Of course, such restrictions should strike a balance between the efficiency gained and the potential to forbid some interesting theorems.

# Existing Work #

Automated theory exploration has been applied to libraries in Isabelle and Haskell, although we focus on the latter as its implementations are the most mature (<span style="font-variant:small-caps;">Hipster</span> actually explores Isabelle by translating code to Haskell first!). Haskell is interesting to target, since its functional purity and algebraic structure make equational properties common; recursion and higher-order functions make automation non-trivial; and since these properties can't be expressed in Haskell itself (without difficulty [@lindley2014hasochism], at least), less effort is spent discovering and proving these properties compared to proof-oriented systems like Isabelle.

Due to Haskell's relative popularity, there are large code repositories such as <span style="font-variant:small-caps;">Hackage</span> available to explore, with the potential to benefit existing library authors and users in comprehending and maintaining their code [@QuickSpec].

Currently, the most powerful TE system for Haskell is <span style="font-variant:small-caps;">HipSpec</span>. This uses <span style="font-variant:small-caps;">QuickSpec</span> to search through *expressions* (combinations of the Haskell terms given by the theory), rather than searching through the space of equations or proofs directly. Expressions are grouped into equivalence classes, such that the <span style="font-variant:small-caps;">QuickCheck</span> counterexample finder cannot distinguish between the elements; equations relating the members of these classes are then conjectured, and sent to existing automated theorem provers to try and prove [@rosen2012proving]. This approach works well as a lemma generation system, making <span style="font-variant:small-caps;">HipSpec</span> a capable inductive theorem prover as well as a theory exploration system [@claessen2013automating].

# Going Forward #

Given this state of the art, we identify the following as potential areas for improvement:

 - Expression enumeration is brute-force; this could scale to larger terms and theories using a heuristic algorithm.
 - "Interestingness" is a fixed part of the algorithm: an equation is interesting if it cannot be derived from previous equations. As we increase the size of our theory, this becomes unsatisfying in two ways:
    - The number of irreducible equations grows, making it desirable to impose extra conditions of a more subjective nature.
    - Surprising, insightful equations may be discarded, if they are actually reducible in some complex, non-obvious way. A more subjective interestingness measure could be used to veto such rejections.
 - The system does not propose candidate equations by data mining previous results; generalisation methods like anti-unification could do this, and at the same time remove the requirement that general forms must be enumerated early.
 - All type-safe combinations of the given expressions are tried, whilst it may be discernable a priori that some combinations are not worth considering (either because they are never related, or because their relations are never interesting). A pre-processor could make large theories more tractable by selecting combinations which are likely to be related, similar to premise selection in automated theorem proving [@kuhlwein2012overview].

We are implementing a system called <span style="font-variant:small-caps;">ML4HS</span> to investigate these ideas. Our initial hypothesis that expressions with similar definitions are more likely to be related by equational properties than those without, and hence a similarity-based clustering method such as that of <span style="font-variant:small-caps;">ML4PG</span> [@journals/corr/abs-1302-6421] can be used to implement a divide and conquor pre-processor.

Since our aim is to scale up theory exploration, we treat entire <span style="font-variant:small-caps;">Hackage</span> packages as our theories. <span style="font-variant:small-caps;">ML4HS</span> will manage downloading, compiling, managing dependencies, etc. automatically. This both eliminates the need to define theories manually, and may be useful in its own right as a mechanism to execute arbitrary Haskell code from arbitrary modules in arbitrary packages.

# Acknowlegements #

I am grateful for those who have helped formulate these ideas through conversation, especially the HipSpec team at Chalmers University (Moa Johansson, Koen Claessen, Nick Smallbone and Dan Rosén) and my supervisor Katya Komendantskaya. I also wish to thank the implementors of the systems we are building on, including HipSpec, QuickSpec and QuickCheck on the theory exploration side, as well as GHC, Cabal and Nix on the infrastructure side.

# References #
