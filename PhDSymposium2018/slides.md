---
title: Quantitative Benchmarking for Conjecture Generation
author: "Chris Warburton (supervisor Alison Pease)"
bibliography: Bibtex.bib
header-includes:
    - \usepackage{tikz}
    - \usetikzlibrary{shapes,backgrounds}
---

# Background #

# Conjecture Generation #

 - Artificial Intelligence task in Formal Systems/Methods
 - Find "interesting properties" of given definitions (theory, model, software)
 - Useful for mathematics, research, education, software engineering, ...
 - What counts as "interesting"?

# Conjecture Generation: Examples #

 - Inverse: `parse (print x) == x`
 - Idempotence: `sort (sort x) == sort x`
 - Equivalence: `bubbleSort x == quickSort x`
 - Identity: `scale 1 x == x`
 - Invariants: `set x y (set x z db) == set x y db`
 - Commuting: `union x y == union y x`

# Conjecture Generation: Non-examples #

 - Definition: `double x == plus x x`
 - Special case: `plus 2 0 == 2`
 - Irrelevance: `validateXML (userName x) == False`
 - Complication: `min (length (reverse (duplicate n x))) 0 == 0`

# Formal Systems and Methods #

 - Foundation for mathematics (in principle)
 - Concrete representation of statements, proofs, deductions, ...
 - Trivial to verify mechanically
 - Closely related to programming (Curry-Howard correspondence)
 - Used by automated reasoning (theorem proving, counterexample finding, ...)
 - Notable examples: Logic programming (Prolog), type systems

# Formal Methods: Achievements #

High-profile examples of formal methods working:

 - CompCert (optimising C compiler) [@leroy2012compcert]
 - AMD5K86 FPU [@brock1996acl2]
 - SEL4 microkernel [@klein2009sel4]
 - Hale's proof of Kepler's Conjecture [@hales2017formal]

# Formal Methods: Missed Opportunities #

High-profile software errors, which formal methods *may* have avoided:

 - Pentium FPU: Missing table entries ($475 million recall)
 - Ariane 5: 64-bit float -> 16-bit int (rocket self-destruct)
 - Therac-25: Race condition (radiation therapy 100x too strong)
 - Patriot missile: Rounding error (missed incoming missile)

# Formal Methods: Problems #

Reasons formal methods aren't industry standard:

 - Difficult (specialist knowledge)
 - Time consuming
 - Fragile (e.g. small changes break proofs)

# Demonstration #

Prove a relatively simple property: `plus x y = plus y x`

Proof requires four additional lemmas:

 - Congruence of `=`: `(x = y) -> (Succ x = Succ y)`
 - Transitivity of `=`: `And (x = y) (y = z) -> (x = z)`
 - Right identity: `plus x Zero = x`
 - This thing: `plus x (Succ y) = Succ (plus x y)`

# Conjecture Generation Example: QuickSpec #

Can we generate these properties automatically?

# Conjecture Generation Example: Fallback #

\begin{scriptsize}
\begin{itemize}
 \item \texttt{plus x y == plus y x}
 \item \texttt{plus x zero == x}
 \item \texttt{plus x (plus y z) == plus y (plus x z)}
 \item \texttt{equal x y == equal y x}
 \item \texttt{equal x x == equal y y}
 \item \texttt{and a b == and b a}
 \item \texttt{and a a == a}
 \item \texttt{and a (and b c) == and b (and a c)}
 \item \texttt{plus x (succ y) == succ (plus x y)}
 \item \texttt{equal x (plus x y) == equal y zero}
 \item \texttt{and a (equal x x) == a}
 \item \texttt{equal x (succ x) == equal y (succ y)}
 \item \texttt{equal (plus x y) (plus x z) == equal y z}
 \item \texttt{and (equal x y) (equal y z) == and (equal x y) (equal x z)}
 \item \texttt{equal (plus x y) (succ y) == equal (plus x z) (succ z)}
 \item \texttt{equal (succ x) (succ y) == equal x y}
 \item \texttt{equal (plus x x) (plus y y) == equal x y}
 \item \texttt{equal zero (succ x) == equal x (succ x)}
 \item \texttt{and (equal x y) (equal x zero) == equal zero (plus x y)}
 \item \texttt{equal (plus x x) (succ zero) == equal x (succ x)}
\end{itemize}
\end{scriptsize}

# Which Properties are Interesting? #

In theory: Unsolved philosophical problem

In practice: Precision/recall analysis

 - Choose some definitions
 - Choose some interesting properties: our *ground truth*
 - Compare generated results to chosen ones

# Precision/Recall Analysis #

> The (ground) truth, the whole truth and nothing but the truth

\def\wantwidth{0.75cm}
\def\madepos{0.8cm}
\def\madewidth{1cm}
\def\want{(0       ,0) circle (\wantwidth)}
\def\made{(\madepos,0) circle (\madewidth)}
\begin{tikzpicture}
  \centering

  \fill[yellow] \want;
  \fill[pink  ] \made;

  \begin{scope}
   \clip        \want;
   \fill[green] \made;
  \end{scope}

  \draw \want;
  \draw \made;

  \node at (-1.5cm,0) {Wanted   };
  \node at ( 3.2cm,0) {Generated};
\end{tikzpicture}

Precision: Proportion of conjectures matching ground truth

\begin{tikzpicture}
  \centering
  \fill[pink] \made;

  \begin{scope}
   \clip        \made;
   \fill[green] \want;
   \draw        \want;
  \end{scope}

  \draw \made;
\end{tikzpicture}

Recall: Proportion of ground truth matching conjectures

\begin{tikzpicture}
  \centering
  \fill[yellow] \want;

  \begin{scope}
   \clip \want;
   \fill[green] \made;
   \draw \made;
  \end{scope}

  \draw         \want;
\end{tikzpicture}

# Precision/Recall Analysis: Ground Truth Example #

Definitions and properties taken from Isabelle theorem prover: $0$,
$\text{Succ}$, $+$ and $\times$

$x + 0 = x$

$x \times 0 = 0$

$x + y = y + x$

$(x + y) + z = x + (y + z)$

$(x \times y) + (z \times y) = (x + z) \times y$

$x + \text{Succ}(y) = \text{Succ}(x + y)$

$x \times \text{Succ}(y) = x + (x \times y)$

$x \times y = y \times x$

$(x \times y) \times z = x \times (y \times z)$

$(x \times y) + (x \times z) = (y + z) \times x$

$\text{Succ}(x) + y = x + \text{Succ}(y)$

$x + (y + z) = y + (x + z)$

# Evaluating Conjecture Generators #

\includegraphics[width=\textwidth]{graphs/table2}

 - Only provides 2 small, unrepresentative data points for each system

# Our Contribution #

 - Use *large* theorem proving benchmarks as ground truth
 - *Sample* sub-sets of definitions to evaluate performance
 - *Aggregate* and *compare* running time, precision and recall

# Our Contribution: Large Ground Truth #

Tons of Inductive Problems theorem prover benchmark [@claessen2015tip]

 - 343 properties of 182 functions
 - Suitable for programming applications (induction, higher order functions, ...)
 - Relevant domains (nat/int/binary arithmetic, regex, heaps, lists, logic, ...)

```
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec acc_plus ((x Nat) (y Nat)) Nat
  (match x (case Z y)
           (case (S z) (acc_plus z (S y)))))
(assert-not (forall ((x Nat) (y Nat))
              (= (acc_plus x y) (acc_plus y x))))
```

# Application: QuickSpec #

\begin{figure}
  \input{graphs/quickspectime.pgf}
  \caption{Time taken by QuickSpec on inputs sampled from TIP. Failures shown in
  red, blue line shows median, error bars show inter-quartile range.}
\end{figure}

# Application: QuickSpec #

\begin{figure}
  \input{graphs/quickspecprec.pgf}
  \caption{Precision and recall of QuickSpec on TIP samples. Line shows ratio of
  averages, sample standard deviation is shaded.}
\end{figure}

# Application: IsaCoSy #

\begin{figure}
  \input{graphs/isacosytime.pgf}
  \caption{Time taken by IsaCoSy on inputs sampled from TIP. Failures shown in
  red, blue line shows median, error bars show inter-quartile range.}
\end{figure}

# Application: IsaCoSy #

\begin{figure}
  \input{graphs/isacosyprec.pgf}
  \caption{Precision and recall of IsaCoSy on TIP samples. Line shows ratio of
  averages, sample standard deviation is shaded.}
\end{figure}

# Application: Comparison #

 - Running time (all samples)
    - SpeedUp Test protocol compares median running times [@touati2013speedup]
    - QuickSpec faster than IsaCoSy 67% - 98% of the time (95% confidence)
 - Recall (only successes)
    - QuickSpec: 37%, IsaCoSy: 25%
    - McNemar's test for contingency tables
    - QuickSpec > IsaCoSy (p = 0.0026)
 - Precision (only successes)
    - QuickSpec: 14%, IsaCoSy: 19%
    - Boschloo's test for proportions
    - No significant difference (p = 0.11)

# Benchmark Drawbacks #

 - Doesn't solve the philosophical issues (what is "interesting"?)
 - Assumes algorithms generalise (e.g. no overfitting)
 - Penalises novel discoveries
 - Doesn't handle continuous/interactive systems

# Future Work #

Our methodology can be extended in several ways:

 - Translating to more languages and tools
 - Incorporating more benchmarks
 - Comparing/incorporating other sources (e.g. textbooks)
 - Competitions?

Our aims:

 - Augment QuickSpec to improve running time and precision
 - Applications to off the shelf software

# Conclusion #

 - Conjecture generation requires better evaluation/comparison
 - We answer this with a practical benchmarking methodology
    - Cross tool and cross language
    - Extensible to other domains, logics, ...
 - Allows some measure of progress
 - Identifies areas for improvement

Code and results available at http://chriswarbo.net/projects/theory-exploration

# References
