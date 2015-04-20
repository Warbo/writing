---
title: Machine Learning for Theory Exploration
author:
- name: Chris Warburton
  affiliation: University of Dundee
  email: cmwarburton@dundee.ac.uk
- name: Ekaterina Komendantskaya
  affiliation: University of Dundee
  email: katya@dundee.ac.uk
documentclass: default
citation-style: acm-sig-proceedings.csl
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
abstract: |
  **Theory Exploration** (TE) aims to automate the tedious yet necessary task of verifying Mathematicians' and programmers' work, but the blind search used by existing approaches limits them to small examples. Meanwhile, huge repositories of formal knowledge are being routinely data-mined for structure and correlation. We provide a method for guiding TE using these abundant statistics, and assess whether this hybrid approach is feasible for tackling problems of a realistic size.

---

#  Introduction

Small mistakes made in Mathematics and programming can cause large problems in the real world. Computer verification can reduce this risk by checking our reasoning step-by-step; but traditional software's inability to follow "obvious" arguments without explicit guidance often makes it impractical. The recent *theory exploration* approach[@buchberger2000theory] tackles this by generating a database of facts about a user-provided "theory" (eg. a software library). This database can either serve as "background knowledge" for a traditional verification tool, to help it follow more coarse-grained proof steps; or it can be queried directly to discover interesting facts about the theory.

Existing TE systems, such as <span style="font-variant:small-caps;">QuickSpec</span>[@QuickSpec] and <span style="font-variant:small-caps;">HipSpec</span>[@Claessen_hipspec:automating], rely on undirected, brute-force search to generate their databases. Although complete, these algorithms' exponential complexity limits their scalability to small theories with only a handful of definitions. To be practical, the technique must be able to work with theories spanning thousands of definitions, without relying on expert users to cherry-pick a sub-set.

**Machine Learning** (ML) offers many scalable techniques for studying large theories, such as *premise selection*[@kuhlwein2012overview]: choosing lemmas which are most likely to help us prove a conjecture. This is similar to our cherry-picking problem, but TE is concerned with a theory's structure rather than individual conjectures.

Theory structure has been studied by <span style="font-variant:small-caps;">ML4PG</span>[@DBLP:journals/corr/abs-1303-1419], using *clustering* to find statistical similarities and hierarchies among definitions. We investigate whether such clustering information can help TE systems navigate large theories more effectively.

# Methodology

Following the approach of <span style="font-variant:small-caps;">QuickSpec</span>, our "theories" are software libraries written in Haskell; a popular programming language where correctness is concerned. We divide these definitions into small clusters, using a similar technique to <span style="font-variant:small-caps;">ML4PG</span>. We then run <span style="font-variant:small-caps;">QuickSpec</span> on each cluster individually, to produce "facts" in the form of equalities relating the definitions. The facts for each cluster are then combined.

We compare the total running time and the resulting database against running <span style="font-variant:small-caps;">QuickSpec</span> on the whole, unclustered library. We observe the tradeoff between speed and completeness, for various library sizes.

# Results

We have developed an ML approach for analysing Haskell code, including a bespoke feature extraction method which, to our knowledge, is the first in the literature. The success of our clustering tool shows the suitability of Haskell for the same statistical approaches used to study other languages.

# Future Work

Our tool can be improved with a more systematic consideration of the design decisions and heuristics used, but the preprocessor approach is inherently limited. A more thorough integration of our methodology into state-of-the-art TE systems would provide more opportunities for exploiting statistical information, and also to "close the loop" by using the TE database to inform the statistical algorithms.

# References
