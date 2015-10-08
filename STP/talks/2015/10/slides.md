# Scaling Automated Theory Exploration in Haskell

<style type="text/css">
body {
  color: #000000;
}
</style>

<table style="width: 100%;">
 <tr>
  <td style="text-align: left;">
   Chris Warburton
  </td>
  <td style="text-align: right;">
   Katya Komendantskaya
  </td>
 </tr>
 <tr style="font-size: 0.8em;">
  <td style="text-align: left;">
   cmwarburton@dundee.ac.uk
  </td>
  <td style="text-align: right;">
   e.komendantskaya@dundee.ac.uk
  </td>
 </tr>
 <tr style="text-align: center;">
  <td colspan="2">
   University of Dundee
  </td>
  </tr>
  <tr style="text-align: center;">
  <td colspan="2">
    Scottish Theorem Proving 2015-10-07
  </td>
  </tr>
</table>

<span style="bottom: 10px; position: absolute; font-size: 0.8em;">
This work was supported by EPSRC grant 1526504 - Machine-Learning Methods in
Functional Programming and Interactive Therorem Proving
</span>

# Theory Exploration #

<div style="width: 100%; text-align: center;">

$(\Sigma, V) \overset{TE}{\rightarrow} \text{Terms}(\Sigma, V)$

</div>

Theory Exploration describes any system for turning a "theory" (signature
and variables) into theorems of that theory, which are *well-formed*, *provable*
and *interesting*.

. . .

## Comparison Criteria ##

 - **How do we generate conjectures?**
 - **How do we guarantee well-formedness?**
 - **How do we prove conjectures?**
 - **What is considered "interesting"?**

# (Interactive) Theory Exploration

> Mathematical theory exploration proceeds by applying, under the guidance of a
> human user, various algorithmic reasoners for producing new formulae from
> given ones and aims at building up (large) mathematical knowledge bases in an
> efficient, reliable, well-structured, re-usable, and flexible way.
> -- (Buchberger 2004)

Example: Theorema

 - **How do we generate conjectures?** User-driven
 - **How do we guarantee well-formedness?** Types and pre-conditions
 - **How do we prove conjectures?** ATP (eg. Otter)
 - **What is considered "interesting"?** User-driven

# Automated Theory Exploration #

> ~~Mathematical~~^Automated^ theory exploration proceeds by applying,
> ~~under the guidance of a human user~~, various algorithmic reasoners for
> producing new formulae from given ones and aims at building up (large)
> mathematical knowledge bases in an efficient, reliable, well-structured,
> re-usable, and flexible way.

Examples: IsaCoSy, Hipster, **HipSpec**

 - **How do we generate conjectures?** QuickSpec: equivalence classes of enumerated expressions
 - **How do we guarantee well-formedness?** Types
 - **How do we prove conjectures?** SMT (eg. Z3)
 - **What is considered "interesting"?** Un-derivable from previous equations

# Why Automated Theory Exploration? #

 - Exposing problematic assumptions ✔
 - Finding simple relationships ✔
 - Autonomous, open-ended, anytime ✔
 - Scales poorly with theory & formula size ✘
 - Can't propose new notions/definitions ✘

. . .

**Problem:** Doesn't seem to align very well with general Mathematics

. . .

**Solution:** Aligns well with *programming*

# Why Haskell? #

 - **Equational**: definitions, rewrite rules & coercions
 - **Pure:** Effects are separate from computation
 - **Strong types**: Algebraic datatypes, parametricity
 - **Popular:** Relatively large code repositories (eg. Hackage)
 - **Already studied:** QuickSpec, HipSpec

Haskell code often follows algebraic laws which Haskell is unable to express!

# Identifying Improvements #

HipSpec is state-of-the-art. How might it be improved?

 - **Well-formedness:** Types work well enough
 - **Proof:** ATP/SMT works well enough

. . .

 - Focus on:
    - **Automation**
    - **Conjecture generation**
    - **Interestingness criteria**

# Automation: ML4HS #

```{pipe="cat > ml4hs.dit"}
/-------\ +----------------------------------------------------+
|Hackage| |ML4HS               +---------+                     |
\-------/ |                 /->|QuickSpec|-\                   |
    |     |                 |  +---------+ |                   |
    V     |                 |              |                   |
 /-----\  |  +------------+ |  +---------+ |  +-------------+  |  /----\
 |Cabal|--|->|Preprocessor|-+->|QuickSpec|-+->|Postprocessor|--|->|User|
 \-----/  |  +------------+ |  +---------+ |  +-------------+  |  \----/
          |                 |              |                   |
          |                 |  +---------+ |                   |
          |                 \->|QuickSpec|-/                   |
          |                    +---------+                     |
          +----------------------------------------------------+
```

```{.unwrap pipe="sh | pandoc -f html -t json"}
ditaa ml4hs.dit ml4hs.png > /dev/null 2> /dev/null
DATA=$(base64 -w 0 < ml4hs.png)
echo "<img src='data:image/png;base64,$DATA' alt='ML4HS' />"
```

 - Modular framework for exploring real Haskell code (not toy examples)
    - Input: name/location of a Haskell package
    - Output: QuickSpec conjectures (send to HipSpec for proofs)

# Automation: ML4HS #

 - Fetch/build dependencies (Nix)
 - Download & build package (Cabal)
 - Extract names & ASTs (GHC plugin)
 - Discard errors:
    - Non-exported names
    - Core artefacts (eg. dictionaries, type params)
    - Ill-typed signatures (eg. if monomorphise fails)
 - Divide: identify related sub-sets
 - Conquer: invoke QuickSpec on each

# Conjecture Generation: Divide and Conquer #

 - Inspired by relevance filtering in Sledgehammer and clustering in ML4PG
 - No need to compare everything to everything else
 - Initial approach: cluster by similarity of ASTs
    - Recurrent clustering, as found in ML4PG

```{pipe="cat > dc.dit"}
              +-----+----+    +--+--+
     map      |"map"|    |    | 4| 0|
    /   \     +-----+----+    +--+--+    +--+--+--+--+--+--+
   $    xs -> |"$"  |"xs"| -> | 2|-1| -> | 4| 0| 2|-1| 4| 3|
  / \         +-----+----+    +--+--+    +--+--+--+--+--+--+
mod  2        |"mod"|"2" |    | 4| 3|
              +-----+----+    +--+--+
```

```{.unwrap pipe="sh | pandoc -f html -t json"}
ditaa -E dc.dit dc.png > /dev/null 2> /dev/null
DATA=$(base64 -w 0 < dc.png)
echo "<img src='data:image/png;base64,$DATA' alt='DC' />"
```


# Conjecture Generation: Future Work #

 - More clustering approaches:
    - Pair-wise relevance filtering (eg. naive bayes)?
    - Off-the-shelf ML classifiers?
 - Enumeration scales exponentially (in theory)
    - In reality: types constrain combinations
    - Search problem: Well-studied in AI
 - Other approaches:
    - Only search previous counterexamples (Graffiti)
    - Best-first search for interestingness (AM, HR)
    - Relevance filtering (Sledgehammer)

# "Interestingness": Future Work

 - Un-derivability is elegant, but misses some intuitions
    - "Non-obvious" reductions
    - Irrelevant/incidental relationships
 - Well-studied in Machine Learning and Data Mining
    - e.g. surprise, utility, novelty, artificial curiosity
 - What kinds of properties do we tend to care about?
    - Look at what we tend to test!
 - More ideas wanted!

# Applications #

 - Lemma generation (eg. HipSpec)
 - Finding redundancy/duplication
 - Aiding debugging/refactoring
 - Finding isomorphisms
 - Finding rewrite rules
 - Finding new typeclasses (instances of "laws")
    - Concept formation may help here too!

# Acknowlegements #

Thank you to the HipSpec team at Chalmers University (Moa Johansson,
Koen Claessen, Nick Smallbone, Dan Rosén and Irene Lobo Valbuena) for useful
discussions of these ideas, and Ouanis Seddaoui for help with our implementation.
