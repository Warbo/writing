---
title: Machine Learning for Theory Exploration
author: Chris Warburton
documentclass: default
citation-style: acm-sig-proceedings.csl
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
abstract: |
  Machine-verified, formal Mathematics is dominated by two complementary approaches: **Interactive Theorem Proving** (ITP) and **Automated Theorem Proving** (ATP). ITP provides a framework for manually developing proofs, whilst ATP can automatically prove "routine" theorems of certain restricted forms.

  There is growing support for these techniques among Computer Scientists and Software Engineers, eg. through the *propositions as types*[@howard1995formulae] relation between ITP and strongly-typed programming.

  Mathematicians (with the notable exception of Homotopy Type Theorists[@voevodsky2013homotopy]) are more skeptical. Buchberger[@buchberger2000theory] suggests this indifference is due to the theorem-proving paradigm being  unrepresentative of the work carried out in mathematical research, teaching and application. In particular, he advocates a more open-ended, less goal-directed paradigm: considering whole collections of definitions, theorems and computations together; rather than trying to prove individual theorems in isolation. This approach is termed **Theory Exploration** (TE), and the sentiment is even echoed within the context of goal-oriented ATP[@fearnley1996automated].

  A key idea in TE is to group conjectures and theorems into "layers", of roughly similar complexity. Once a layer is sufficiently understood, or "completed" (eg. with a decision procedure), it can be assimilated into our knowledge base and used in the definition and completion of subsequent layers.

  Since Buchberger's <span style="font-variant:small-caps;">Theorema</span> system, which requires much manual definition, there has been a wave of more 'autonomous' TE systems: <span style="font-variant:small-caps;">IsaCoSy</span>[@johansson2009isacosy] and <span style="font-variant:small-caps;">Hipster</span>[@Hipster] target the Isabelle ITP; <span style="font-variant:small-caps;">QuickSpec</span>[@QuickSpec] and <span style="font-variant:small-caps;">HipSpec</span>[@Claessen_hipspec:automating] target the Haskell programming language. In these systems, the notion of a new "layer" is an equation which cannot be derived from the knowledge base through rewriting. This is a reasonable definition, yet to discover these equations each system relies on an undirected brute-force search. Whilst ensuring completeness and outperforming other ATPs on induction problems, this exponential search fundamentally limits their scalability beyond toy examples with a handful of definitions.

  Exponential problems, brute-force algorithms and approximate solutions have been studied extensively in the fields of **Artificial Intelligence** (AI) and **Machine Learning** (ML). In this work we introduce ML methods to existing TE systems in a conservative way. In particular, we use previous work from the <span style="font-variant:small-caps;">ML4PG</span> system (Machine Learning for Proof General) and its derivatives to break up large theories into small clusters of similar definitions, which are more manageable by existing TE systems yet rich enough to yield novel, non-trivial relationships.

  **RESULTS??**

  This approach requires a few ad-hoc heuristics to determine which information to extract and how it should influence the decisions. These were determined empirically, although a systematic investigation of the possibilities and their influence would be a useful followup.

  The directness of our approach allows meaningful comparison to existing work, which is important when tasks are open-ended and hard to quantify. However, the performance opportunities available to preprocessors and wrappers are limited compared to a more thorough symbiosis of symbolic and statistical techniques. This would provide a fruitful area for future research.

---

# References
