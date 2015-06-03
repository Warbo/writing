---
title: Machine Learning for Formal Languages
author: Chris Warburton
---

# Premise Selection #

Most widely used application, eg. Naive Bayes in Isabelle's Sledgehammer

Given a set of axioms, lemmas, theorems, etc. select those which are *relevant* to proving a particular goal

Prevents Automated Theorem Provers slowing down as more theorems are proved

# Strategy Selection #

Alter ATP parameters using evolutionary algorithms, eg. BliStr

Mainly applied to reproving and benchmarks (eg. TPTP), rather than "real work"

# Inductive Functional Programming #

Derive a function from input/output pairs

**or**

Derive a value of a given type, using Curry Howard, eg. *MagicHaskeller*

Uses Monte Carlo search to eliminate duplicates, similar to *QuickSpec*

# ML4PG #

Unsupervised clustering: carve up libraries based on similarity

Present users with similar definitions, and automata which reproduce proofs

Mixes feature extraction with clustering

# Demo #

# ML4HS #

Apply similar clustering as ML4PG to Haskell

Use results to bias *theory exploration*, looking for theorems and typeclasses/instances

*QuickSpec* uses Monte Carlo search, but only to approximate equality checking rather than for sampling the search space

# Demo? #

# Future Ideas #

Auto-encoders for feature extraction, eg. as a benchmark

PageRank-style graph algorithms to find "important" definitions

Many-armed bandit strategies for concurrent search/exploration

Data-mining proof/test libraries to model what programmers care about

Inductive Functional Programming for theory exploration
