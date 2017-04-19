---
title: Exploring Software with Symbolic and Statistical Algorithms
author: |
  Chris Warburton<br/>
  Supervisors: Alison Pease, Ekaterina Komendantskaya
link-citations: true
bibliography: /home/chris/Writing/Bibtex.bib
---

# Overview #

```{pipe="tee renderPic.sh" style="display: none;"}
#!/usr/bin/env bash

cat > $1.dit
ditaa "$1.dit" "$1.png" > /dev/null 2> /dev/null
DATA=$(base64 -w 0 < "$1.png")
echo "<img src='data:image/png;base64,$DATA' alt='$1' />" |
  pandoc -f html -t json
```

 - Motivation and Aims `chmod +x renderPic.sh`{pipe="sh" style="display: none;"}
 - Intro to Haskell
 - Symbolic: Theory Exploration (TE)
 - Statistical: Recurrent Clustering
 - Combining the two
 - Conclusion

# General Motivation #

 - Modern software is large, complex and costly to maintain
 - Existing analyses mostly confirm/refute expected properties (e.g. "the length of a list is not negative"):
    - *Testing* is cheap, but only covers a few cases
    - *Verifying* is expensive, but covers all cases
 - *(Theory) Exploration* finds properties which may be *unexpected*
    - Not biased by our assumptions
    - Can inform refactoring, optimisation, verification, learning...
    - Can we make it cheap?

# Our Aims #

 - Reduce difficulties in applying TE:
    - Assess impact of more informed search strategies on computational cost
    - Plug TE systems into existing interfaces/representations
 - Extend TE capabilities:
    - More subjectively "interesting", or "useful" results
    - Mining data generated during TE runs, e.g. to discover abstractions or predicates

# Intro to Haskell #

Defining datatypes:

```haskell
data List a = Nil
            | Cons a (List a)

```

Defining functions:

```haskell
append  Nil        y = y
append (Cons x xs) y = Cons x (append xs y)
```

Calling functions (e.g. from an interpreter):

```haskell
> append (Cons 1 Nil) (Cons 2 (Cons 3 Nil))
Cons 1 (Cons 2 (Cons 3 Nil))
```

# Why Haskell? #

Haskell is well suited to exploration:

 - Strong mathematical base:
    - Compiles into System F~C~ (a variant of lambda calculus) [@sulzmann2007system]
    - Corresponds (via Curry-Howard) to intuitionistic logic, but unsound
    - Type system is algebraic
    - Encourages algebraic style for functions
    - Polymorphism leads to "free theorems"
    - Many other niceties

# Why Haskell? #

Haskell is well suited to exploration:

 - Purity:
    - Actions, like deleting files, are *values*
    - Actions can be manipulated and combined, but only one (`main`{.haskell}) is executed
    - No side-effects, so arbitrary code is safe to run [@terei2012safe]

Combine numeric values using `+`{.haskell} (addition) to get a new numeric value:

```haskell
10 + 5
```

Combine action values using `>>`{.haskell} (sequencing) to get a new action value:

```haskell
print "hello" >> print "world"
```

# Why Haskell? #

Haskell is well suited to exploration:

 - Laziness:
    - Without side-effects, the order of evaluation doesn't matter
    - Allows "lazy" (call by need) evaluation, which works "back to front"
    - If a normal form exists, lazy evaluation will find it
    - Lets us ignore most computational/control issues

For example,

```haskell
fst (x, y) == x
```

This is true for *all* `x`{.haskell} and `y`{.haskell}, even if `y`{.haskell} triggers an exception or an infinite loop.

# Why Haskell? #

Haskell is well suited to exploration:

 - Existing infrastructure:
    - Package manager (Cabal)
    - Compiler with plugin mechanism (GHC)
    - Metaprogramming facilities (Template Haskell)
    - Code and data generators (QuickCheck [@claessen2011quickcheck])
    - Theory exploration systems! (QuickSpec)

# Theory Exploration (QuickSpec) #

QuickSpec [@QuickSpec] is a Theory Exploration system for Haskell code:

## Input ##

A *signature* of Haskell values and variables

``` haskell
[length, reverse, append, +, x, y]
```

## Output ##

Conjectured equations, relating elements of the signature

``` haskell
           length x == length (reverse x)
length (append x y) == length x + length y
reverse (reverse x) == x
                ... == ...
```

These conjectures can be proved separately, e.g. by `HipSpec` [@Claessen_hipspec:automating]

# Theory Exploration (QuickSpec) #

## How it Works ##

 - Enumerate all (well-typed) combinations of the signature's elements, up to a fixed size
    - `[length, reverse, append, +, x, y, length x, length y, reverse x, ...]`
 - Group together expressions of the same type.
 - Set the variables to random values, evaluate all of the expressions and check whether all elements in each group are equal; if not, split up the group.
    - NOTE: This would be very dangerous in an impure language!
 - After a hundred tests without splitting any groups, stop.
 - For each group, choose an element and conjecture that it equals all the others.
 - Simplify the equations to remove special cases

# Theory Exploration (QuickSpec) #

## Pros ##

 - Procedure is complete: all equations will be found
 - Given a signature, the rest is automated
 - Plugs into other tools, e.g. Isabelle theorem prover

## Cons ##

 - Increasing the signature size, or the maximum expression size, requires exponentially more time
 - Values must be manually chosen, written into a signature and annotated (e.g. with arity)

Can we automate the selection of values, e.g. from a whole application, so that signatures aren't too big to explore?

# Recurrent Clustering #

Tries to group arbitrary expressions together based on similarity. Applied to theorem provers, such as Coq [@journals/corr/abs-1212-3618] and ACL2 [@heras2013proof]

Two problems:

 - Expressions have recursive structure; doesn't fit neatly into, say, feature vectors.
 - Most expressions are simple combinations of others; we need to handle these references.

Two solutions:

 - Flatten expressions into vectors, trying to maintain alignment of sub-expressions.
 - Use clustering to handle references; this leads to a recursive algorithm.

# Recurrent Clustering: Flattening Expressions #

Convert the Haskell code into "Core", a syntax for System F~C~:

```{.haskell style="font-size: 0.8em;"}
append = Lam a (Lam y (Case (Var (Local a))
                            b
                            (Alt DataAlt (Var Constructor) (Var (Local y)))
                            (Alt DataAlt (App (App (Var Constructor) (Var (Local x)))
                                              (Var (Local xs)))
                                         (App (App (Var Constructor) (Var (Local x)))
                                              (App (App (Var (Global append))
                                                        (Var (Local xs)))
                                                   (Var (Local y)))))))
```

```{pipe="cat > out.tex" style="display: none;"}
\documentclass[]{article}

\usepackage[paperheight=9in,paperwidth=3in,margin=0in,landscape]{geometry}

\usepackage{lmodern}
\usepackage{listings}
\usepackage{amssymb,amsmath}
\usepackage{paralist}
\usepackage{tikz-qtree}
\usepackage{ifxetex,ifluatex}
\usepackage{fixltx2e} % provides \textsubscript
\ifnum 0\ifxetex 1\fi\ifluatex 1\fi=0 % if pdftex
  \usepackage[T1]{fontenc}
  \usepackage[utf8]{inputenc}
\else % if luatex or xelatex
  \ifxetex
    \usepackage{mathspec}
    \usepackage{xltxtra,xunicode}
  \else
    \usepackage{fontspec}
  \fi
  \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
  \newcommand{\euro}{€}
\fi
% use upquote if available, for straight quotes in verbatim environments
\IfFileExists{upquote.sty}{\usepackage{upquote}}{}
% use microtype if available
\IfFileExists{microtype.sty}{%
\usepackage{microtype}
\UseMicrotypeSet[protrusion]{basicmath} % disable protrusion for tt fonts
}{}
\ifxetex
  \usepackage[setpagesize=false, % page size defined by xetex
              unicode=false, % unicode breaks when used with xetex
              xetex]{hyperref}
\else
  \usepackage[unicode=true]{hyperref}
\fi
\urlstyle{same}  % don't use monospace font for urls
\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt plus 2pt minus 1pt}
\setlength{\emergencystretch}{3em}  % prevent overfull lines
\setcounter{secnumdepth}{5}
\newcommand{\feature}[1]{\phi(#1)}
\newcommand{\id}[1]{\texttt{"#1"}}
\newcommand{\CVar}{\texttt{Var}}
\newcommand{\CLit}{\texttt{Lit}}
\newcommand{\CApp}{\texttt{App}}
\newcommand{\CLam}{\texttt{Lam}}
\newcommand{\CLet}{\texttt{Let}}
\newcommand{\CCase}{\texttt{Case}}
\newcommand{\CType}{\texttt{Type}}
\newcommand{\CLocal}{\texttt{Local}}
\newcommand{\CGlobal}{\texttt{Global}}
\newcommand{\CConstructor}{\texttt{Constructor}}
\newcommand{\CLitNum}{\texttt{LitNum}}
\newcommand{\CLitStr}{\texttt{LitStr}}
\newcommand{\CAlt}{\texttt{Alt}}
\newcommand{\CDataAlt}{\texttt{DataAlt}}
\newcommand{\CLitAlt}{\texttt{LitAlt}}
\newcommand{\CDefault}{\texttt{Default}}
\newcommand{\CNonRec}{\texttt{NonRec}}
\newcommand{\CRec}{\texttt{Rec}}
\newcommand{\CBind}{\texttt{Bind}}

\begin{document}
\begin{figure}
      \begin{tikzpicture}[sibling distance=0pt]
        \tikzset{sibling distance=0pt}
        \tikzset{level distance=20pt}
        \Tree[ .$\CLam$
                $\id{a}$
                [ .$\CLam$
                   $\id{y}$
                   [ .$\CCase$
                      [ .$\CVar$
                         [ .$\CLocal$
                            $\id{a}$ ]]
                      $\id{b}$
                      [ .$\CAlt$
                         $\CDataAlt$
                         [ .$\CVar$
                            $\CConstructor$ ]
                            [ .$\CVar$
                               [ .$\CLocal$
                                  $\id{y}$ ]]]
                      [ .$\CAlt$
                         $\CDataAlt$
                         [ .$\CApp$
                            [ .$\CApp$
                               [ .$\CVar$
                                  $\CConstructor$ ]
                               [ .$\CVar$
                                  [ .$\CLocal$
                                     $\id{x}$ ]]]
                            [ .$\CVar$
                               [ .$\CLocal$
                                  $\id{xs}$ ]]]
                         [ .$\CApp$
                            [ .$\CApp$
                               [ .$\CVar$
                                  $\CConstructor$ ]
                               [ .$\CVar$
                                  [ .$\CLocal$
                                     $\id{x}$ ]]]
                            [ .$\CApp$
                               [ .$\CApp$
                                  [ .$\CVar$
                                     [ .$\CGlobal$
                                        $\id{append}$ ]]
                                  [ .$\CVar$
                                     [ .$\CLocal$
                                        $\id{xs}$ ]]]
                               [ .$\CVar$
                                  [ .$\CLocal$
                                     $\id{y}$ ]]]]]]]]
      \end{tikzpicture}
\end{figure}
\end{document}
```

```{.unwrap pipe="bash"}
set -e
pdflatex out 1>&2
[[ -f "out.pdf" ]] || {
  echo "No out.pdf file was made" 1>&2
  exit 1
}

convert -density 150 out.pdf -quality 90 out.png
[[ -f "out.png" ]] || {
  echo "No out.png file was made" 1>&2
  exit 1
}

DATA=$(base64 -w 0 < "out.png")
echo "<img width="100%" src='data:image/png;base64,$DATA' alt='Tree' />" |
  pandoc -f html -t json
```

# Recurrent Clustering: Flattening Expressions #

Arrange tree-structed expression into matrix:

```{.unwrap pipe="./renderPic.sh Matrix"}
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| Lam         |             |        |             |         |     |     |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| a           | Lam         |        |             |         |     |     |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| y           | Case        |        |             |         |     |     |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| Var         | b           | Alt    | Alt         |         |     |     |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| Local       | DataAlt     | Var    | Var         | DataAlt | App | App |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| a           | Constructor | Local  | App         | Var     | App | App |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| y           | Var         | Var    | Local       | Var     | Var | App | Var   |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
| Constructor | Local       | xs     | Constructor | Local   | Var | Var | Local |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
|x            | x           | Global | Local       | y       |     |     |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
|append       | xs          |        |             |         |     |     |       |
+-------------+-------------+--------+-------------+---------+-----+-----+-------+
```

Then concatenate the rows (padded with 0):

```{.unwrap pipe="./renderPic.sh Vector"}
+-----+---+---+---+---+---+---+---+---+-----+---+---+---+---+---+---+---+------+---+--
| Lam | 0 | 0 | 0 | 0 | 0 | 0 | 0 | a | Lam | 0 | 0 | 0 | 0 | 0 | 0 | y | Case | 0 | ...
+-----+---+---+---+---+---+---+---+---+-----+---+---+---+---+---+---+---+------+---+--
```

# Recurrent Clustering: Calculating Features #

 - "Keywords", like `Lam`, `App`, `Case`, etc. are given fixed numbers.
 - Local variables, e.g. `y`, are given *de Bruijn indices*: at each occurrence, we count how many times we've been nested in a `Lam`.
 - Global variables, like `Nil`, `append`, etc. are harder:
    - Topologically sort expressions in dependency order: if `A` references `B`, then `B` comes first. If `A` and `B` are mutually recursive, they occur at the same level.
    - Cluster all expressions in the first group. Any references (which must be from mutual recursion) get a fixed "recursion" value.
    - Append the next group of expressions. If a referenced expression was just clustered, use it's cluster index. If not, use the "recursion" value.
    - Repeat, until all expressions have been clustered.

# Recurrent Clustering for Theory Exploration #

```{.unwrap pipe="./renderPic.sh ML4HS"}
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

 - Read all definitions from a Haskell package
 - Use similarity, determined by recurrent clustering, to break up into many small signatures
 - Explore all concurrently
 - Combine the results

# Current Work #

Measuring performance on the *Tons of Inductive Problems* (TIP) theorem prover benchmark:

 - Precision/recall:
    - How many of our conjectures are TIP benchmarks?
    - How many of the TIP benchmarks do we conjecture?
    - How does the amount of splitting affect the performance, in terms of equations and time?
 - How do QuickSpec and ML4HS compare as we vary the number of benchmark expressions included in the signature?
 - How does recurrent clustering compare to other similarity measures?

# Future Directions #

 - Customise the exploration algorithm, rather than working around it.
 - Consider other ML algorithms, e.g. kernel methods for comparing expressions.
 - Consider other "interestingness" criteria, rather than only eliminating special cases.
 - Move beyond equations, e.g. conditional equations, predicate invention, etc.

# Conclusion #

Theory Exploration is a promising approach to improve automation in quality assurance, software maintenance, verification, optimisation, etc.

New techniques are needed, both the scale up the capabilities of TE systems and to reduce the manual effort required to invoke them.

Our work approaches both of these, by sacrificing completeness for a reduced search space, and by interfacing TE tools more directly with the Haskell packaging infrastructure.

Quantitative results are pending, as to the effect of each parameter and the impact of overheads.

# Questions? #

# References #
