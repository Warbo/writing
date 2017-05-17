---
title: Quantitative Benchmarking for Theory Exploration
author: |
  Chris Warburton<br/>
  University of Dundee<br/>
  c.m.warburton@dundee.ac.uk
link-citations: true
bibliography: /home/chris/Writing/Bibtex.bib
---

# Motivation #

 - Automated mathematical *calculation* is routine
 - Automated mathematical *proof* is common in some fields (e.g. programming)
 - Automated mathematical *exploration* is rare

. . .

Why exploration?

 - Aids understanding/proving/etc. of a theory/library
 - Opportunity to move expertise into tools
 - Can *surprise* us

# (Automated) Theory Exploration #

 - Takes as input a set of definitions in some formal language
    - e.g. a functional programming library:

```
append(nil, ys)         = ys
append(cons(x, xs), ys) = cons(x, append(xs, ys))
   map(f, nil)          = nil
   map(f, cons(x, xs))  = cons(f(x), map(f, xs))
```

 - Outputs interesting conjectures about those definitions
    - e.g. `map` distributes over `append` (interesting for parallel computation)

```
map(f, append(xs, ys)) = append(map(f, xs), map(f, ys))
```

. . .

Problems:

 - Inefficient (e.g. uses brute-force)
 - Ambiguous goals/definitions (e.g. what is "interesting"?)

# Research Questions #

 1. How do we evaluate conjectures?
    - Finding theorems is trivial!

 2. How do we evaluate/compare sets of conjectures?
    - We want to find more than one conjecture
    - Repeating a good conjecture 100 times isn't a good set!

 3. How do we evaluate/compare theory exploration systems?
    - Brute-force can optimise anything
    - How do we compare "practical" performance?

# Q1. Evaluating Conjectures

What is "interesting"?

. . .

In theory:

 - Important for evaluating performance in novel domains
 - Many competing/complementary measures proposed
 - Some objective (e.g. statement vs proof size), some subjective (e.g. compression progress)

. . .

In practice:

 - Existing tools are far from human performance
 - Comparing tool's output to human's output is challenge enough
 - Simplifying assumptions:
    - Exploration method doesn't overfit to a particular theory
    - Results on known theories should generalise to novel ones
    - For known theories, "interesting" ~= "appears in existing corpus"

# Q2. Evaluating Sets of Conjectures

Given a well-studied theory and a corpus of known theorems/conjectures

# Existing Systems #

 - Generating conjectures in first order logic (e.g. Graffiti, HR)
 - Our focus is higher-order logic (functional programming, proof assistants)
 - Three main systems for HOL:
    - IsaCoSy in Isabelle, uses constraint solving
    - IsaScheme in Isabelle, uses templates/schemas
    - QuickSpec in Haskell, uses testing
        - Used by Hipspec and Hipster
TODO: use author names as references?

# Existing Evaluations #

 - Isabelle libraries used as corpus
 - Compare IsaCoSy, IsaScheme and Hipspec (QuickSpec)

. . .

Problems:

 - Only two theories used (natural numbers and lists)
 - Theories are small
    - Natural numbers: 4 definitions, 12 statements
    - Lists: 6 definitions, 9 statements

# Our Approach #

 - Use a larger corpus of definitions and statements
 - Generate theories of a desired size (number of definitions) by sampling
 - Automate the whole exploration and evaluation process:
    - Sample a theory
    - Translate into a tool's native format
    - Set up the tool
    - Time the exploration process
    - Extract conjectures
    - Compare to corpus

. . .

Benefits:

 - Empirical, statistical evaluations and comparisons
 - Focuses on efficiency problems, by sampling larger sizes
 - Provides an unambiguous goal for implementors

# Our Corpus #
TODO: Maybe change heading, etc. to show WHY TIP? and WHAT WE'VE DONE
Our definitions and statements are taken from the TIP theorem proving benchmark:

 - Separates definitions from theorem statements
 - Order of magnitude larger than before (219 definitions, 343 statements)
 - Higher-order (e.g. includes `map`)
 - Includes problems from the theorem proving literature
 - Includes problems relevant to programming/verification
 - Simple format, with tools for translation to Haskell, Isabelle, etc.
 - Not written by us (no cheating!)

# Our Corpus #

We transform TIP from theorem proving to theory exploration:

 - Pool together all definitions (~3500)
 - Add constructor/destructor functions for each datatype
 - Remove duplicates (leaves 269)
 - Provide uniform sampling of definitions (such that > 0 applicable theorems)
 - Provide the theorems applicable to a given sample

# Illustration #

We have applied our benchmarking methodology to the Qui......

QUICKSPEC GRAPH

RECALL GRAPH

PAIRWISE DIFFERENCE (QUICKSPEC VS ISACOSY)?

# Observations #

 - Runtime depends heavily on the theory contents
    - TODO: Use pairwise difference to compare
 - High variance (mostly very fast or very slow), increasing with theory size
 - Lots of room for improvement!

TODO: Come back to questions, with answers

# advantages/benefits (remaining problems)

TODO: Rename
 - New approaches needed to reduce runtime and variance
 - Recall

# Idea 1: Bucketing #

 - Smaller theories tend to be faster
 - If we're given a large theory, split it into many smaller "buckets"
 - Initial approach: bucket "randomly", to see what effect it has

# Idea 2: Relevance Filtering #

 - Used in theorem proving to choose which lemmas seem relevant to proving a
   conjecture.
 - We have no conjecture to begin with, but maybe we can use the definitions?
 - Algorithms:
    - Recurrent clustering

# Future Work #

 - Machine learning
    - Using benchmark corpus as training data
    - Using benchmark as fitness function
    - Careful to avoid overfitting!
 - Extending to other implementations/languages
 - Use benchmark to evaluate/compare new approaches
 - Study applications of theory exploration to realistic problems
    - Lemma generation has been studied
    - Program optimisation
    - Abstraction discovery

# Resources #

All code available at chriswarbo.net/git and github.com/Warbo

 - `theory-exploration-benchmarks`: TIP -> theory exploration converter
 - `haskell-te`: Benchmarking for QuickSpec
 - `isaplanner-tip`: Benchmarking for IsaCoSy
 - `mlspec`: Runs QuickSpec on buckets

All results (modulo hardware speed) are reproducible using Nix. Please let me
know if you have any problems!

# Questions? #

# References #
