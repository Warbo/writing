---
title: Machine Learning Introduction
---

# Machine Learning #

<!-- Umar Syed -->

> The study and design of algorithms that improve with experience

<!-- Ray Solomonoff -->

> Getting good approximations to ideal probabalistic prediction

# Major Applications #

**Classification:** Assign a *label* (element of a finite set) to every value

**Prediction:** Given a sequence, output the next element of the sequence

**Compression:** Given values $x$, output a small model which can recreate $x$

**Search:** Given a predicate $P$, output an $x$ such that $P(x)$

**Optimisation:** Given a *fitness function* $f$, output $argmin(f)$

**Function approximation:** Given various $x$ and $f(x)$, output $f$

**Function inversion:** Given $f$ and $x$, output $y$ such that $f(y) = x$

**Reinforcement learning:** Output *actions* to maximise $reward$

# Some Definitions #

**Supervised vs Unsupervised:** There is/isn't a ground truth

**Positive vs Negative examples:** Outputs we do/don't want

<!-- For example: separate cats from dogs vs clustering -->

**Online vs Offline:** Inputs received sequentially/in batch

**Underfitting vs Overfitting:** Missed/phantom patterns

# Example Applications #

Spam filter:

 - Classification (labels are "spam" and "ham")
 - Online (emails arrive sequentially)
 - Supervised ("spam" and "ham" have ground truths)

Dividing a collection of sentences into N 'clusters':

 - Classification (labels are "1", "2", ..., "N")
 - Offline (we have the whole collection)
 - Unsupervised (the meaning of a label comes from its elements)

# Major Approaches #

**Connectionist:** Models are graphs

 - Learning adjusts connectivity/architecture/weight
 - Examples: Artificial Neural Networks, Bayesian Networks

**Kernel methods:** Models are 'feature spaces'

<!-- Dot-product spaces (similarity) OR distance spaces (dissimilarity) -->

 - Learning adjusts (normals of) hyperplanes in the space
 - Example: Support Vector Machines

**Evolutionary computation:** Models are programs

 - Learning combines the fittest in a *population*
 - Example: Genetic Algorithms, Genetic Programming

# ANNs #

```{pipe="dot -Tpng | base64 -w 0 > ann.b64"}
digraph {
  I1 -> H1
  I1 -> H2
  I2 -> H1
  I2 -> H2
  I3 -> H2
  I3 -> H3
  I4 -> H2
  I4 -> H3
  I5 -> H3
  I5 -> H4
  I6 -> H3
  I6 -> H4
  H1 -> O1
  H1 -> O2
  H2 -> O1
  H2 -> O2
  H3 -> O1
  H3 -> O2
  H4 -> O1
  H4 -> O2
}
```

```{.unwrap pipe="sh | pandoc -f markdown -t json" align="center"}
printf '<img alt="" src="data:image/png;base64,'
cat ann.b64
printf '" />'
```

Input signals propagate forwards, from *input* to *hidden* to *output*

*Error* signals propagate backwards, from *output* to *hidden* to *input*

# ANNs #

**Key idea:** All ANNs are *differentiable*

*Backpropagation* uses derivatives to assign credit/blame, adjusting weights accordingly

Example of *gradient descent* learning

Trivial to implement with *automatic differentiation*

Suffers from **vanishing gradient problem**

# Naive Bayes #

```{pipe="dot -Tpng | base64 -w 0 > naive.b64"}
digraph {
  Class -> A1
  Class -> A2
  Class -> A3
  Class -> A4
  Class -> "..."
}
```

```{.unwrap pipe="sh | pandoc -f markdown -t json" align="center"}
printf '<img alt="" src="data:image/png;base64,'
cat naive.b64
printf '" />'
```

> Naive Bayes is the simplest form of Bayesian network, in which all attributes are independent given the value of the class variable.

Terrible at estimating probabilities, but excellent at binary classification

<!--

Bayes: $p(c|E) = {p(E|c)\*p(c) \over p(E)}$

Naive bayes: $f(E) = {p(C = L1) \over p(C = L2)} \* PRODUCT{i=1, n} of {p(xi | C = L1) \over p(xi | C = L2)}$

Because: p(E|c) = p(x1, x2, ..., xn|c) = PRODUCT{i=1, n} p(xi|c)

-->

# Genetic Programming #

```{pipe="dot -Tpng | base64 -w 0 > gen.b64"}
digraph {
  A1 [label="+"]
  A2 [label="*"]
  A3 [label="x"]
  A4 [label="2"]
  A1 -> 5
  A1 -> A2
  A2 -> A3
  A2 -> A4
  B1 [label="+"]
  B2 [label="-"]
  B3 [label="x"]
  B4 [label="2"]
  B1 -> 7
  B1 -> B2
  B2 -> B3
  B2 -> B4
  C1 [label="..."]
}
```

```{.unwrap pipe="sh | pandoc -f markdown -t json" align="center"}
printf '<img alt="" src="data:image/png;base64,'
cat gen.b64
printf '" />'
```

Keep a *population* of programs: prefer fitter solutions

Prune the population, then fill back up with mutants and "children"

No vanishing gradient, but rather ad-hoc and slow

# Combinations #

Mixture of experts

Dynamic portfolios

Boosting

Deep learning

Meta-learning
