---
bibliography: Bibtex.bib
---

# Quantitative Benchmarking for Conjecture Generation #

Chris Warburton

Supervisor: Alison Pease

# Background #

# Conjecture Generation #

 - Artificial Intelligence task in Formal Systems/Methods
 - Find "interesting" properties of a given set of definitions
 - Useful for theorem proving, verification, specification, education, ...

# Formal Systems and Methods #

 - Foundation for mathematics (in principle)
 - Concrete representation of statements, proofs, deduction, ...
 - Closely related to programming (Curry-Howard correspondence)
 - Used by automated reasoning (theorem proving, counterexample finding, ...)

# Formal Systems and Methods #

Notable achievements:

 - CompCert (optimising C compiler) [@leroy2012compcert]
 - AMD5K86 FPU [@brock1996acl2]
 - SEL4 microkernel [@klein2009sel4]
 - Hale's proof of Kepler's Conjecture [@hales2017formal]

Problem:

 - Difficult (specialist knowledge)
 - Time consuming
 - Fragile (e.g. small changes break proofs)

# Motivating Example: x + y = y + x #

# Motivating Example: Fallback #

Prove a relatively simple property: `plus x y = plus y x`

Proof requires four additional lemmas:

 - Congruence of `=`: `(x = y) -> (Succ x = Succ y)`
 - Transitivity of `=`: `And (x = y) (y = z) -> (x = z)`
 - Right identity: `plus x Zero = x`
 - `plus x (Succ y) = Succ (plus x y)`

# Conjecture Generation Example: QuickSpec #

Can we generate these statements automatically?

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

# Evaluating Conjecture Generators #

 - In theory: Unsolved philosophical problem
 - In practice: Precision/recall analysis
    - Choose ground truth properties for some definitions
    - Generate conjectures for those definitions
    - Precision: Proportion of conjectures matching ground truth
    - Recall: Proportion of ground truth matching conjectures

# Evaluating Conjecture Generators: Ground Truth #

Isabelle theorems about $0$, $\text{Succ}$, $+$ and $\times$:

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

\includegraphics[width=\textwidth]{graphs/table}

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
  \caption{Precision (left) and recall (right) of QuickSpec on TIP samples.
  Line shows ratio of averages, sample standard deviation is shaded.}
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
  \caption{Precision (left) and recall (right) of IsaCoSy on TIP samples.
  Line shows ratio of averages, sample standard deviation is shaded.}
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

# Drawbacks #

 - Doesn't solve the philosophical issues (what is "interesting"?)
 - Penalises novel discoveries
 - Doesn't handle continuous/interactive systems

# Future Work #

 - Translating to more languages and tools
 - Incorporating more benchmarks
 - Comparison with other sources (e.g. textbooks)
 - Competitions?

# Conclusion #

 - We define a practical benchmarking methodology
 - Cross tool and cross language
 - Extensible to other domains, logics, ...
 - Allows robust comparison between approaches/implementations

Available at https://github.com/Warbo/theory-exploration-benchmarks

# References
