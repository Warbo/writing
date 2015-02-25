---
title: Dimensionality Reduction, Distributed Representations and Learning Structured Data
bibliography: ~/Documents/ArchivedPapers/Bibtex.bib
---

Many machine learning algorithms require all their input values to have the same, fixed size. For example, popular learning algorithms for artificial neural networks (ANNs) such as **backpropagation** [@Russell:2003:AIM:773294] use a fixed graph of nodes and edges, and only adjust the *weight* associated with each edge.

This poses a problem when the size of each input is not known, may vary and may even be unbounded. For example, in the case of **online** learning we must make predictions/decisions before seeing all of the inputs. Unbounded input appears in domains such as proof automation, where a theorem may be a tree of unbounded depth. In these situations we need a (possibly lossy) technique to normalise all inputs to a standard, fixed size which is amenable to learning. These fixed-size representations are called **features** and the normalising process is known as **feature extraction**. Without loss of generality we will assume our features to be vectors of $N$ bits, since this is a universal format relevant to real implementations.

## Truncation and Padding ##

The simplest way to limit the size of our inputs is to truncate anything larger than a particular size (and pad anything smaller). This is the approach taken by ML4PG [@journals/corr/abs-1302-6421], which limits itself to trees with at most 10 levels and 10 elements per level; each tree is converted to a $30 \times 10$ matrix (3 values per tree node) and learning takes place on these normalised representations.

Truncation is unsatisfactory in the way it balances *data* efficiency with *time* efficiency. Specifically, truncation works best when the input data contains no redundancy and is arranged with the most significant data first (in a sense, it is "big-endian"). The less these assumptions hold, the less we can truncate. Since many learning algorithms scale poorly with input size, we would prefer to eliminate the redundancy using a more aggressive algorithm, to keep the resulting feature size as low as possible.

## Dimension Reduction ##

A more sophisticated approach to the problem of reducing input size is to view it as a **dimension reduction** technique: our inputs can be modelled as points in high-dimensional spaces, which we want to project into a lower-dimensional space ($\left\{ {0, 1} \right\}^N$ in the case of $N$-bit vectors).

Truncation is a trivial dimension reduction technique: take the first $N$ coordinates (bits). More sophisticated projection functions consider the *distribution* of the points, and project with the hyperplane which preserves as much of the variance as possible (or, equivalently, reduces the **mutual information** between the points).

There are many techniques to find these hyperplanes, such as *Principle Component Analysis* and *auto-encoding*; however, since these techniques are effectively machine learning algorithms in their own right, they suffer some of the same constraints we're trying to avoid:

 - They operate *offline*, requiring all input points up-front
 - All input points must have the same dimensionality

In particular, the second constraint is precisely what we're trying to avoid. Sophisticated dimension reduction is still useful for *compressing* large, redundant features into smaller, information-dense representations, and as such provides a good complement to truncation.

The requirement for offline "batch" processing is more difficult to overcome, since any learning we perform for feature extraction will interfere with the core learning algorithm that's consuming these features. Such systems are possible, but out of scope for this small initial implementation.

## Structured Data ##

The task of dimension reduction changes when we consider *structured* data. Recursive structures, like trees, have *fractal* dimension: increasing the size of a recursive structure gives us more *fine-grained* features, rather than *orthogonal* features.

To eliminate the fractional dimension of structured input, we can *fold* the structure using some *combining function*. For proof automation we are concerned with tree structures of the following form:

\begin{displaymath}
  Tree = \left\{
           \begin{array}{l l}
             leaf(\mathbf{F})      & \quad \text{where $\mathbf{F}$ is a feature}\\
             branch(L, R) & \quad \text{where $L$ and $R$ are trees}
           \end{array}
         \right.
\end{displaymath}

Following [@zanzotto2012distributed] we choose **circular convolution**, denoted $\odot$, as our combining function. Hence, to reduce a tree of features $T$ to a single feature, we can use the following fold operation:

\begin{displaymath}
  \begin{split}
    reduce(leaf(\mathbf{F}))      & = \mathbf{F}
    \\
    reduce(branch(L, R)) & = reduce(L) \odot reduce(R)
  \end{split}
\end{displaymath}

We use circular convolution due to the following desirable properties:

 - **Non-commutative**: $A \odot B  \not\approx B \odot A$, hence we can distinguish between $branch(A, B)$ and $branch(B, A)$
 - **Non-associative**: $A \odot (B \odot C) \not\approx (A \odot B) \odot C$, hence we can distinguish between $branch(A, branch(B, C))$ and $branch(branch(A, B), C)$

Here we use $\not\approx$ to represent that these quantities differ *with high probability*, based on empirical testing. This is the best we can do, since the type of combining functions $(Feature \times Feature) \rightarrow Feature$ has a co-domain strictly smaller than its domain, and hence it must discard some information. In the case of circular convolution, the remaining information is spread out among the bits in the resulting feature, which is known as a **distributed representation** [@plate1991holographic].

### Extracting Features from Coq ###

Prior to 2014-09-08, the Coq proof assistant provided a rudimentary XML import/export feature, which we can use to access tree structures for learning. We achieve this by using the `external`{.ocaml} primitive of the Ltac tactic language: `external "cmd" "arg" t1 t2 t3.`{.ocaml} will run the shell command `cmd`, passing the string `arg` as an argument. We can provide any number of Coq terms, here shown as `t1`, `t2` and `t3`, which will be serialised to XML and sent to the shell command's standard input. The standard output can be used to send instructions back to Coq, but we'll ignore that feature for now.

```{pipe="tee process.sh"}
#!/bin/sh
xml=$(cat /dev/stdin)
hash=$(echo "$xml" | md5sum)
echo "$xml" > "${hash}.xml"
echo "$xml" | processor 8 > "${hash}.feature"
echo '<CALL uri="idtac" />'
```

```{pipe="sh"}
chmod +x process.sh
```

```{pipe="tee nats.v"}
Goal True.

```

```{pipe="sh"}
for n in {0..255}
do
  echo 'try (external "./process.sh" "6" ' >> nats.v
  echo "$n"                             >> nats.v
  echo ')  || idtac. '                  >> nats.v
done

echo 'tauto. Qed.' >> nats.v
```

```{pipe="sh"}
coqc nats.v 2> err || true
```

## Sequencing ##

Any investigation of variable-size input would be incomplete without mentioning the *sequencing*. This is a lossless approach, which splits the input into fixed-size *chunks*, which are fed into an appropriate ML algorithm one at a time. The sequence is terminated by a sentinel; an "end-of-sequence" marker which, by construction, is distinguishable from the data chunks. This technique allows us to trade *space* (the size of our input) for *time* (the number of chunks in a sequence).

Not all learning algorithms can be adapted to accept sequences. One notable approach is to use **recurrent ANNs** (RANNs), which allow arbitrary connections between nodes, including cycles. Compared to **feed-forward** ANNs (FFANNs), which are acyclic, the *future output* of a RANN may depend arbitrarily on its *past inputs* (in fact, RANNs are universal computers).

The main problem with RANNs, compared to the more widely-used FFANNs, is the difficulty of training them. If we extend the standard backpropagation algorithm to handle cycles, we get the **backpropagation through time** algorithm [@werbos1990backpropagation]. However, this suffers a problem known as the **vanishing gradient**: error values decay exponentially as they propagate back through the cycles, which prevents effective learning of delayed dependencies, undermining the main advantage of RANNs. The vanishing gradient problem is the subject of current research, with countermeasures including **neuroevolution** (using evolutionary computation techniques to train an ANN) and **long short-term memory** (LSTM; introducing a few special, untrainable nodes to persist values for long time periods [@hochreiter1997long]).

# References #
