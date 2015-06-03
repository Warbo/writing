---
title: Machine Learning for Theory Exploration
author: Chris Warburton
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
---

# Software for Maths and Programming #

<img src="resources/LaTeX_logo.png" alt="" height=100 />
<img src="resources/Sage_logo_new.png" alt"" height=100 />
<img src="resources/MediaWiki-smaller-logo.png" alt"" width=300 />
<img src="resources/Git-logo.png" alt"" height=100 />
<img src="resources/Coq_logo.png" alt"" width=150 />

# Theory Exploration #

 - Software to aid Mathematicians and Programmers
    - Based on a model of peoples' workflows
 - A **theory** is a set of "building blocks" (functions, formulae, objects, etc.)
    - eg. programs and software libraries
 - **Explore** how blocks fit together
    - No explicit goal, just do what's "interesting"

# Theory Exploration: Analogy #

Given *building blocks*

<img src="resources/blocks.png" alt="" height="20" />

Look for interesting combinations

<img src="resources/blocks_comb.png" alt="" height="208" />

# Theory Exploration: Example #

Given *building blocks*

```haskell
append    length
reverse   x        y
```

Look for interesting combinations

```haskell
length  (reverse x)  = length x

reverse (reverse x)  = x

reverse (append x y) = append (reverse y)
                              (reverse x)
```

# Demo? #

# Problem: Scaling #

Existing implementations (IsaCoSy, QuickSpec, HipSpec, Hipster) rely on brute-force search

 - Exponential complexity
 - Limits the number of blocks (~10 in practice)
 - Limits the size of combinations (depth ~4 in practice)

Real libraries may contain hundreds of definitions!

# Solution: Machine Learning #

Focus search on promising combinations:

 - Analyse source code of blocks
 - *Cluster* blocks based on statistical similarity
 - Explore one cluster at a time

# Solution: Machine Learning #

Current status:

 - Haskell parser
 - Feature extraction (count symbol occurences)
 - Clustering

TODO:

 - Handle module imports
 - Turn clusters into theories
 - Evaluate equations found compared to unclustered approach

# Future Directions #

 - Different feature extractors
 - Different ML algorithms
 - Feed TE database into the learning process
 - Measure quality of discoveries, as well as quantity

# Applications #

 - Quality Assurance
    - Automatic verification (of "obvious" properties)
 - Optimisation/redundancy/reuse
 - Discovering abstractions/patterns
    - New patterns
    - Instances of existing patterns

# Questions? #
