---
title: Machine Learning for Theory Exploration
author: Chris Warburton
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
header-includes:
    - \usepackage[T1]{fontenc}
    - \usepackage{upquote}
---

# Abstract #

**Theory exploration** (TE) takes a *theory* (a collection of definitions) and *searches* for interesting theorems. Compared to the traditional state-then-prove approach to theorem proving, TE is more autonomous and has the potential to discover theorems beyond those conjectured by the user.

Unfortunately, this lack of goals also makes it difficult to explore theories of a practical size. We suggest that machine learning techniques can mitigate this problem: using statistical analysis to infer what makes a theorem "interesting" and which areas of the search space to concentrate on.

# Introduction #

We consider the task of exploring software libraries in the Haskell programming language. Haskell is interesting to study, since its purity and algebraic structure make it amenable to a formal treatment, yet its emphasis on recursion and higher-order functions make it difficult to do so automatically.

Haskell's balance of correctness and usability means code is often subject to algebraic laws, either knowingly or unknowingly, which cannot be expressed in the language itself (without difficulty[@lindley2014hasochism], at least). Such laws may benefit library authors and users (eg. for comprehension, optimisation or simplification). This makes repositories of Haskell code like <span style="font-variant:small-caps;">Hackage</span> a tremendous source of rich, structured information.

\newcommand\mdoubleplus{\ensuremath{\mathbin{+\mkern-6mu+}}}

Whilst separate languages and tools can be used to *prove* a conjectured law[@rosen2012proving], we focus on the task of automatically *finding* these candidates in the first place. This "bottom-up theory exploration" problem[@RISC1482] has been tackled in Haskell by the <span style="font-variant:small-caps;">HipSpec</span> tool, which uses approximate reasoning and brute-force search to generate candidate laws, which are verified using traditional methods.

Specifically, <span style="font-variant:small-caps;">HipSpec</span> (building on the work of <span style="font-variant:small-caps;">QuickSpec</span>) enumerates type-correct Haskell expressions built out of pre-specified components. The <span style="font-variant:small-caps;">QuickCheck</span> counter-example finder is used to distinguish between these expressions; those which cannot be separated (eg. `False`{.haskell} and `not True`{.haskell}) are conjectured to be equal. Attempts are then made to prove these conjectures.

This approach works well as a lemma generation system, making <span style="font-variant:small-caps;">HipSpec</span> a capable inductive theorem prover[claessen2013automating]. However, enumerating terms by brute-force limits the technique to small, carefully-chosen sets of components (AKA *theories*); and prevents scaling to tasks such as discovering unknown structure in and across <span style="font-variant:small-caps;">Hackage</span> packages.

This scaling issue can be tackled in several ways; here we choose to keep the theory exploration framework unchanged, and instead consider methods to automate the "theory selection" task: that careful choosing of components to study. This is similar to the *premise selection* task[@kuhlwein2012overview] in automated theorem proving, as both must compute some approximate "relevance" measure across a large space of symbolic structures. Yet the differences are significant: premise selection has a pre-specified target to compare against, which theory selection lacks; similary, premise selection is associated with a definite fitness criterion (the success or failure of the subsequent proof attempt), whilst "success" is not so clear in theory exploration.

These underspecified, approximate criteria make theory selection a clear candidate for machine learning techniques.

# Machine Learning #

Machine learning, defined by Alpaydin[alpaydin2014introduction] as "programming computers to optimize a performance criterion using example data or past experience", is an increasingly popular discipline for tackling problems which lack a clear algorithmic treatment. A classic example is spam filters, which can be inferred via straightforward statistical methods[graham2002plan] despite the complexity and subtlety of the emails being classified.

## Evaluating Performance ##

From this definition, it is clear that we must choose some performance criterion and some example data. The performance of our selection process depends on the performance of the subsequent exploration phase, which in turn should include factors such as the number of properties discovered, the time taken and the information content of those properties.

## Clustering ##



# Methodology #

We have built a tool called ML4HS (Machine Learning for Haskell). This modular framework performs several tasks:

 - Extracting syntax trees from Haskell packages, using a custom plugin for the Glasgow Haskell Compiler.
 - Discarding definitions which QuickSpec does not accept.
 - Performing feature extraction and clustering of the remaining definitions.
 - Constructing QuickSpec theories and invoking their exploration.

We use the ML4HS framework for all experiments; the machine learning phases are optional, so we ignore them when benchmarking QuickSpec on its own. We use version 4.8 of the Haskell `base` library as our input, since it is widely used and very large, and thus an attractive target for library authors to explore in conjunction with their own packages.

First we measure QuickSpec's performance without any clustering, in order to determine the effect of theory size and search depth on performance. We generate smaller approximations of the `base` package in three ways: `base-uniform-N` discards definitions uniformly across the modules, until it contains `N` definitions; `base-good-N` preferentially discards definitions which appear in the fewest equations; `base-bad-N` preferentially discards definitions appearing in the most equations. We can expect real libraries of size `N` to perform somewhere between `base-good-N` and `base-bad-N`.

Performance is measured as the average rate of equation discovery $\overline R_e = {N_e \over T}$, where $N_e$ is the total number of equations discovered and $T$ is the total time taken. We must use averages, since QuickSpec operates in stages: producing a large number of "raw" equations, then removing redundancies.

We use these benchmarks to determine effective parameter values for our machine learning experiments, which use a k-means clustering algorithm consist of a randomised clustering algorithm

# Results #

# Conclusion and Future Work #

# References #
