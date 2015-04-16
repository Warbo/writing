---
title: Machine Learning for Theory Exploration
author: Chris Warburton
documentclass: default
citation-style: acm-sig-proceedings.csl
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
abstract: |
  Computer-assisted, formal Mathematics is dominated by two complementary approaches: **Interactive Theorem Proving** and **Automated Theorem Proving**. Whilst gaining popularity among Computer Scientists, Mathematicians remain skeptical. **Theory Exploration** provides an alternative to the theorem-proving paradigm, which corresponds more closely to the way Mathematics is practiced; however, the potential of existing exploration systems is limited by their reliance on brute-force search. We propose the use of statistical techniques from Machine Learning to make theory exploration feasibile in real-world domains.

---

#  Introduction

*Theorem proving* is the dominant paradigm in computer-assisted formal Mathematics: the *interactive* approach (ITP) provides a "book-keeping" framework to manage and check manually-written proofs; whilst the *automated* approach (ATP) can prove "routine" theorems, of certain restricted forms, with little manual intervention. Both are *goal-directed*: they assume the prior selection of some interesting, plausible conjecture which the user would like to prove. This is comparable to software development tools, which assume the user is trying to solve some pre-specified problem.

There is growing support for theorem proving systems among Computer Scientists and Software Engineers. In particular, the *propositions as types*[@howard1995formulae] principle blurs the distinction between theorem proving and software development, leading to an influx of ITP techniques in areas like strongly-typed programming.

Mathematicians (with the notable exception of Homotopy Type Theorists[@voevodsky2013homotopy]) are more skeptical. Buchberger[@buchberger2000theory] suggests this indifference is due to the theorem-proving paradigm being unrepresentative of the work carried out in mathematical research, teaching and application. In particular, he advocates a more open-ended, less goal-directed framework: considering whole collections of definitions, theorems and computations together; rather than trying to prove individual theorems in isolation. This is the Theory Exploration (TE) paradigm, and the sentiment is even echoed within the goal-oriented ATP community[@fearnley1996automated].

To retain some focus and direction in the absence of an explicit goal, TE begins with a collection of definitions and relationships (a "theory"; for example, an equational definition of Peano arithmetic). Conjectures about these definitions are grouped into "layers" of roughly similar complexity, and tackled all at once. When a layer is sufficiently understood, or "completed" (eg. with a decision procedure), it can be placed alongside the original definitions to form the basis of a new layer. Hence progress can be made through the successive definition and completion of layers, without any particular layer being specified *a priori*.

Since Buchberger's <span style="font-variant:small-caps;">Theorema</span> system, which requires much manual definition, there has been a wave of more 'autonomous' TE systems: <span style="font-variant:small-caps;">IsaCoSy</span>[@johansson2009isacosy] and <span style="font-variant:small-caps;">Hipster</span>[@Hipster] target the Isabelle ITP; <span style="font-variant:small-caps;">QuickSpec</span>[@QuickSpec] and <span style="font-variant:small-caps;">HipSpec</span>[@Claessen_hipspec:automating] target the Haskell programming language. In these systems, the notion of a new "layer" is an equation which cannot be derived from the knowledge base through rewriting. This is a reasonable definition, yet to discover these equations each system relies on an undirected brute-force search. Whilst ensuring completeness and outperforming other ATPs on induction problems, this exponential search fundamentally limits their scalability beyond toy examples with a handful of definitions.

Exponential problems, brute-force algorithms and approximate solutions have been studied extensively in the fields of **Artificial Intelligence** (AI) and **Machine Learning** (ML). In this work we introduce ML methods to existing TE systems in a conservative way. In particular, we use previous work from the <span style="font-variant:small-caps;">ML4PG</span> system (Machine Learning for Proof General) and its derivatives to break up large theories into small clusters of similar definitions, which are more manageable by existing TE systems yet rich enough to yield novel, non-trivial relationships.

# Methodology

Our approach does not modify existing systems. Instead, we provide a pre-processing layer which analyses a theory's definitions and produces smaller clusters which are more amenable to the brute-force approach. By carefully choosing the features used for comparison, we aim to preserve interesting relationships within these small clusters, whilst eliminating the least promising areas of the search space. This allows the technique to scale to much larger theories than are currently practical.

We choose Haskell as both an implementation language and to represent our theories: definitions correspond to standard Haskell constants, whilst relationships are captured by boolean predicate functions (a sub-set of those used by QuickCheck).

# RESULTS

# Future Work

Wrapping existing systems allows meaningful comparisons to be made to previous work, which is important when tasks are open-ended and hard to quantify. However, the performance opportunities available to preprocessors and wrappers are limited compared to a more thorough symbiosis of symbolic and statistical techniques. For example, our feature extraction technique is oblivious to the equations discovered in previous exploration layers.

# References
