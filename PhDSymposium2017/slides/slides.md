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

# Existing Approaches #

 - Generating conjectures in first order logic (e.g. Graffiti, HR)
 - Our focus is higher-order logic (functional programming, proof assistants)
 - Three main systems for HOL:
    - IsaCoSy: Isabelle, constraint solving [@johansson2009isacosy]
    - IsaScheme: Isabelle, templates/schemas [@montanoscheme]
    - QuickSpec: Haskell, random testing [@QuickSpec]
        - Used by Hipspec[@claessen2013automating] and Hipster[@Hipster]

# Questions #

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
 - Many competing/complementary measures proposed [@colton2000notion]
 - Some objective (e.g. statement vs proof size), some subjective (e.g.
   compression progress)

. . .

In practice:

 - Existing tools are far from human performance
 - Comparing tool's output to human's output is challenge enough
 - Simplifying assumptions:
    - For known theories, "interesting" ~= "appears in existing corpus"
    - Performance should generalise to novel theories (modulo overfitting)

# Q2. Evaluating Sets of Conjectures

Given a corpus of known theorems/conjectures and a set of proposed conjectures:

 - Precision is % of proposed which are in corpus
 - Recall is % of corpus which was proposed
 - Used in previous work

# Existing Evaluations #

 - Isabelle libraries used as corpus
 - Compare IsaCoSy, IsaScheme and Hipspec (QuickSpec)

. . .

Problems:

 - Only two theories used (natural numbers and lists)
 - Theories are small
    - Natural numbers: ~4 definitions, 12 theorems
    - Lists: ~6 definitions, 9 theorems

```{.unwrap pipe="sh | pandoc -f html -t json"}
printf '<img src="data:image/png;base64,'
base64 -w0 < "$TABLE_IMAGE"
printf '" />'
```

# Our Proposal #

 - Use a larger corpus of definitions and statements
 - Generate theories of a desired size (number of definitions) by sampling
 - Identify corpus theorems involving those definitions
 - Average precision/recall over many samples

. . .

Benefits:

 - Replaces ambiguity with empirical, numerical measurements
 - Shows variance
 - More likely to generalise

# Q3. Evaluating Systems

 - No single objective to maximise
    - Are we prepared to wait longer for quality?
 - Important criteria:
    - Precision
    - Recall
    - Run time
    - Variance
    - Scaling behaviour

. . .

Sampling theories from a large corpus provides two opportunities:

 - Pairwise difference of systems, given the same samples
 - Measure scaling by varying #definitions in the samples

# Corpus Source #

We chose the TIP theorem proving benchmark [@claessen2015tip]

 - Separates definitions from theorem statements
 - Order of magnitude larger than before (219 definitions, 343 statements)
 - Higher-order (e.g. includes `map`)
 - Includes problems from the theorem proving literature
 - Includes problems relevant to programming/verification
 - Simple format, with translation to Haskell, Isabelle, etc.
 - Not written by us (no cheating!)

# Generating Our Corpus #

 - Pool together all definitions (~3500)
 - Add constructors/destructors for datatypes
 - Remove duplicate definitions (leaves 269)
 - Sampler for definitions (with > 0 theorems)
 - Query theorems for a given sample

 - We also provide automate the whole exploration and evaluation process:
    - Sampling
    - Translating to appropriate language
    - Timing exploration
    - Extracting conjectures from output
    - Comparing to corpus

# Example #

We have applied our benchmarking methodology to QuickSpec

```{.unwrap pipe="sh"}
# | pandoc -f html -t json
jq -sR '[{"unMeta":{}},[{"t":"RawBlock","c":["html",.]}]]' < /home/chris/Writing/PhDSymposium2017/abstract/runtimes.svg
#printf '[{"unMeta":{}},[{"RawBlock":{"Format":"html"}}
#echo "<html><body>"
#cat /home/chris/Writing/PhDSymposium2017/slides/runtimes.svg
#echo "</body></html>"
#printf '<img src="/home/chris/Writing/PhDSymposium2017/slides/runtimes.svg" />'
#printf '<img src="data:image/svg;base64,'
#base64 -w0 < /home/chris/Writing/PhDSymposium2017/slides/runtimes.svg
#printf '" />'
```

# Observations #

 - Lots of room for improvement!
 - Runtime depends heavily on the theory contents
 - High variance (mostly very fast or very slow), increasing with theory size
 - ~85% take <200s
 - Above 200s, most time out
 - Further investigation needed:
    - What causes a long-running theory?
    - Precision/recall: Currently 0%, corpus querying too coarse-grained

# Potential Improvement #

 - QuickSpec tries every combination of the inputs
 - Choosing a *subset* to explore improves efficiency by avoiding useless
   combinations
    - Incomplete, reduces recall
 - Need *smart* ways to choose subsets
    - Combine *relevance filtering* with *recurrent clustering*
 - Currently implemented: experiments pending

# Summary #

 1. How do we evaluate conjectures?
    - Use known theories and look up in corpus

 2. How do we evaluate/compare sets of conjectures?
    - Precision/recall against large corpus

 3. How do we evaluate/compare theory exploration systems?
    - Repeated sampling from a large benchmark
    - Gather statistics on runtime, precision and recall
    - Compare systems using pairwise difference

 4. Narrowing down search space can improve efficiency

# Future Work #

 - Extending to other implementations/languages
 - Use benchmark to evaluate/compare new approaches
 - Machine learning
    - Benchmark as training data
    - Benchmark as fitness function
    - Hygiene to avoid overfitting!
 - Study applications of theory exploration to realistic problems
    - Lemma generation has been studied
    - Program optimisation
    - Abstraction discovery

# Resources #

All code available at chriswarbo.net/git and github.com/Warbo

 - `theory-exploration-benchmarks`: TIP -> theory exploration converter
 - `haskell-te`: Benchmarking for QuickSpec
 - `isaplanner-tip`: Benchmarking for IsaCoSy
 - `mlspec`: Exploring subsets

All results (modulo hardware speed) are reproducible using Nix. Please let me
know if you have any problems!

# Questions? #

# References #
