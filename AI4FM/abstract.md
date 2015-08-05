---
title: Scaling Automated Theory Exploration
author: Chris Warburton
bibliography: /home/chris/Documents/ArchivedPapers/Bibtex.bib
header-includes:
    - \usepackage[T1]{fontenc}
    - \usepackage{upquote}
---

# Abstract #

**Theory exploration** (TE) takes a collection of definitions (a *theory*) and *searches* for interesting theorems. Compared to the traditional state-then-prove approach to theorem proving, TE has the capability of being more autonomous and discovering theorems beyond those conjectured by the user. Despite severe limits on the search depth, automated exploration is still promising for situations where expert human effort is impractical, such as discovering invariants in large software libraries.

Unfortunately, TE's lack of explicit goals also makes exploring theories of a practical size difficult. We discuss the challenges to scaling up automated theory exploration and suggest approaches to avoid or mitigate them.

# Introduction #

The framework of *theory exploration* (TE) is, by design, nothing more or less than software support for traditional Mathematical workflows; namely, deriving "interesting" consequences from formal definitions[@RISC1482]. Early implementations like <span style="font-variant:small-caps;">Theorema</span>[@buchberger2000theory] emphasised interactivity, in a similar way to computer algebra systems like <span style="font-variant:small-caps;">Mathematica</span> (in which <span style="font-variant:small-caps;">Theorema<span> is implemented) or interactive theorem provers. Subsequent systems have investigated *automated* theory exploration, for tasks such as lemma discovery[@Hipster].

Such automation is difficult for two reasons: as a search problem, TE has poor time complexity; secondly, the search criterion itself is underspecified: what constitutes an "interesting" result?

# Defining "Interesting" #

We refer to the *ideal* output of a TE system as "interesting", although this is too subjective to define precisely. For real implementations, we must choose some exact, computable proxy; in existing systems, this is intimately connected to the choice of search algorithm, to ensure tractability. For example, <span style="font-variant:small-caps;">IsaCoSy</span>[@johansson2009isacosy] discovers equations, which are defined as "interesting" if they cannot be simplified using previously discovered equations. The intuition for such criteria is to avoid special cases of known theorems, such as $0 + 0 = 0$, $0 + 1 = 1$, etc. when we already know $\forall x. 0 + x = x$.

In such systems, we would like general forms to be considered *before* special cases. We can also consider data mining approaches, which infer general rules *after* considering their special cases. Alternative measures of "interestingness" for this context are surveyed in [@geng2006interestingness], which may be adapted to a TE setting. These include objective measures, eg. based on information theory, and subjective measures which ask for the user's opinion. We can also use existing proof libraries and test suites as oracles, in place of user interaction; this has been used as a precision-recall measure to evaluate the performance of <span style="font-variant:small-caps;">HipSpec</span>[@claessen2013automating].

# Tackling Complexity #

Theory exploration is a "bottom-up" process: new theorems are derived from axioms and previous theorems; there is no special "goal" theorem(s) as found in interactive theorem proving, and hence no "landmark" to aim for in the search space. The only knowledge we have is our (proxy) "interesting" criterion: if this is discrete (eg. boolean), we have a *search* problem, if it is continuous, we have an *optimisation* problem. In either case, the complete, brute-force enumeration techniques used by existing TE systems cannot scale to theories of a significant size.

Fast, approximate approaches to search and optimisation are well studied in Artificial Intelligence and Machine Learning[@blum2011hybrid]. Even with a slow search algorithm, we can limit the number of allowed combinations either using a precise type system, or by partitioning the theory into small independently-searched sub-theories. Of course, such restrictions should strike a balance between the efficiency gained and the potential to forbid some interesting theorems.

# Implementations and Applications #

Automated theory exploration has been applied to Isabelle and Haskell, although Haskell has seen the most attention (<span style="font-variant:small-caps;">Hipster</span> actually explores Isabelle by translating code to Haskell!). Haskell is interesting to target, since its functional purity and algebraic structure make equational properties common; recursion and higher-order functions make automation non-trivial; and since these properties can't be expressed in Haskell itself (without difficulty[@lindley2014hasochism], at least), less effort is spent discovering and proving these properties compared to, say, dependently typed languages[@chlipala2011certified].

Due to Haskell's relative popularity, we can explore large code repositories such as <span style="font-variant:small-caps;">Hackage</span>, with the potential to benefit existing library authors and users, for example with comprehension, optimisation or simplification of their code.

\newcommand\mdoubleplus{\ensuremath{\mathbin{+\mkern-6mu+}}}

Haskell TE tools such as <span style="font-variant:small-caps;">HipSpec</span> generate conjectures using testing, which are then sent to existing theorem provers[@rosen2012proving]. These conjectures are equations, which have withstood several rounds of random testing from the QuickCheck system. This approach works well as a lemma generation system, making <span style="font-variant:small-caps;">HipSpec</span> a capable inductive theorem prover[claessen2013automating]. However, enumerating terms by brute-force limits the technique to small, carefully-chosen sets of components (AKA *theories*); and prevents scaling to tasks such as discovering unknown structure in and across <span style="font-variant:small-caps;">Hackage</span> packages.

This scaling issue can be tackled in several ways; here we choose to keep the theory exploration framework unchanged, and instead consider methods to automate the "theory selection" task: that careful choosing of components to study. This is similar to the *premise selection* task[@kuhlwein2012overview] in automated theorem proving, as both must compute some approximate "relevance" measure across a large space of symbolic structures. Yet the differences are significant: premise selection has a pre-specified target to compare against, which theory selection lacks; similary, premise selection is associated with a definite fitness criterion (the success or failure of the subsequent proof attempt), whilst "success" is not so clear in theory exploration.

These underspecified, approximate criteria make theory selection a clear candidate for machine learning techniques.

# Machine Learning #

Machine learning, defined by Alpaydin[alpaydin2014introduction] as "programming computers to optimize a performance criterion using example data or past experience", is an increasingly popular discipline for tackling problems which lack a clear algorithmic treatment. A classic example is spam filters, which can be inferred via straightforward statistical methods[graham2002plan] despite the complexity and subtlety of the emails being classified.

## Evaluating Performance ##

From this definition, it is clear that we must choose some performance criterion and some example data. The performance of our selection process depends on the performance of the subsequent exploration phase, which in turn should include factors such as the number of properties discovered, the time taken and the information content of those properties.

## Clustering ##



# Methodology #

We have built a tool called ML4HS (Machine Learning for Haskell). This modular framework performs several tasks:

 - Extracting syntax trees from Haskell packages, using a custom plugin for the Glasgow Haskell Compiler (GHC).
 - Discarding definitions which <span style="font-variant:small-caps;">QuickSpec</span> does not accept.
 - Performing feature extraction and clustering of the remaining definitions.
 - Constructing <span style="font-variant:small-caps;">QuickSpec</span> theories and invoking their exploration.

We use the ML4HS framework for all experiments; the machine learning phases are optional, so we ignore them when benchmarking <span style="font-variant:small-caps;">QuickSpec</span> on its own. We use version 4.8 of the Haskell `base` library as our input, since it is widely used and very large, and thus an attractive target for library authors to explore in conjunction with their own packages.

First we measure <span style="font-variant:small-caps;">QuickSpec</span>'s performance without any clustering, in order to determine the effect of theory size and search depth on performance. We generate smaller approximations of the `base` package in three ways: `base-uniform-N` discards definitions uniformly across the modules, until it contains `N` definitions; `base-good-N` preferentially discards definitions which appear in the fewest equations; `base-bad-N` preferentially discards definitions appearing in the most equations. We can expect real libraries of size `N` to perform somewhere between `base-good-N` and `base-bad-N`.

Performance is measured as the average rate of equation discovery $\overline R_e = {N_e \over T}$, where $N_e$ is the total number of equations discovered and $T$ is the total time taken. We must use averages, since <span style="font-variant:small-caps;">QuickSpec</span> operates in stages: producing a large number of "raw" equations, then removing redundancies.

We use these benchmarks to determine effective parameter values for our machine learning experiments, which use a k-means clustering algorithm consist of a randomised clustering algorithm

# Results #

# Conclusion and Future Work #

# References #
