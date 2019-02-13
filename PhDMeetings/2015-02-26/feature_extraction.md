---
title: Feature Extraction for Structured Data
bibliography: ~/Documents/ArchivedPapers/Bibtex.bib
header-includes:
    - \DeclareMathOperator{\md5}{MD5}
---

<!-- Helper scripts -->

## Feature Extraction ##

**Feature extraction** is a common pre-processing step for machine learning (ML). Rather than feeding "raw" data straight into our ML algorithm, we only learn a sample of *relevant* details, known as **features**. This has two benefits:

 - **Feature vectors** (ordered sets of features) are chosen to be more compact than the data they're extracted from: feature extraction is *lossy compression*. This reduces the size of the ML problem, improving efficiency (eg. running time).
 - We avoid learning irrelevant details such as the encoding system used, improving *data* efficiency (the number of samples required to spot a pattern).

Another benefit of feature extraction is to *normalise* the input data to a fixed-size representation. Many ML algorithms only work with fixed-size inputs; for example, the popular **backpropagation** [@Russell:2003:AIM:773294] algorithm works on models with *fixed* topology (eg. **artificial neural networks** with fixed connections between nodes). This requires some form of pre-processing in domains where the size of each input is not known, may vary or may even be unbounded.

For example, in the case of **online** learning we must make predictions/decisions before seeing all of the inputs. Unbounded input appears in domains such as programming and theorem proving, where individual term may be trees of unbounded depth. In these situations we need a mapping from arbitrary inputs to a fixed representation which is amenable to learning.

### Significance ###

As an example, say we want to learn relationships between the following program fragments:

(@maybe) `data Maybe a = Nothing | Just a`{.haskell pipe="tee maybe.hs"}

(@either) `data Either a b = Left a | Right b`{.haskell pipe="tee either.hs"}

We might hope our algorithm discovers relationships like:

 - Both (@maybe) and (@either) are valid Haskell code.
 - Both (@maybe) and (@either) describe datatypes.
 - Both datatypes have two constructors.
 - Fragment (@either) is a generalisation of (@maybe) (we can define `Maybe a = Either () a`{.haskell} and `Nothing = Left ()`{.haskell}).
 - There is a symmetry in (@either): `Either a b`{.haskell} is equivalent to `Either b a`{.haskell} if we swap occurences of `Left`{.haskell} and `Right`{.haskell}.
 - It is trivial to satisfy (@maybe) (using `Nothing`{.haskell}).
 - It is not trivial to satisfy (@either); we require an `a`{.haskell} or a `b`{.haskell}.

However, this is too optimistic. Without our domain-knowledge of Haskell, an ML algorithm cannot impose any structure on (@maybe) or (@either), and will treat them as:

```{pipe="sh | tee maybe.bin"}
xxd -b maybe.hs  | cut -c10-62 | tr -d ' '
```

and:

```{pipe="sh | tee either.bin"}
xxd -b either.hs | cut -c10-62 | tr -d ' '
```

respectively. Our high-level hopes are obscured by low-level details: the desirable patterns of Haskell types are mixed with undesirable patterns of ASCII bit sequences, of letter frequency in English words, and so on.

### Practical Considerations ###

In theory we could throw more computing resources and data at a problem, but available hardware and corpora are always limited. Instead, feature extraction lets us narrow the ML problem to what we, with our domain knowlege, consider important.

There is no *fundamental* difference between raw representations and features: the identity function is a valid feature extractor. Likewise, there is no crisp distinction between feature extraction and machine learning: a sufficiently-powerful learner doesn't require feature extraction, and a sufficiently-powerful feature extractor doesn't require any learning!^[Consider a classification problem, to assign a label $l \in L$ to each input. If we only extract a single feature $f \in L$, we have solved the classification problem without using a separate learning step.]

Rather, the terms are distinguished for purely *practical* reasons: by separating feature extraction from learning, we can distinguish straightforward, fast data transformation (feature extraction) from complex, slow statistical analysis (learning). This allows for modularity, separation of concerns, and in particular allows "off-the-shelf" ML to be re-used across a variety of different domains.

Even if we have no domain knowledge, we can still use a feature extraction phase to improve efficiency: first we learn a compact representation for our data, for example using **autoencoding**; then we use that encoder as a feature extractor for our main learning task.

## Truncation and Padding ##

The simplest way to limit the size of our inputs is to truncate anything larger than a particular size (and pad anything smaller). This is the approach taken by ML4PG [@journals/corr/abs-1302-6421], which limits itself to trees with at most 10 levels and 10 elements per level; each tree is converted to a $30 \times 10$ matrix (3 values per tree node) and learning takes place on these normalised representations.

Truncation is unsatisfactory in the way it balances *data* efficiency with *time* efficiency. Specifically, truncation works best when the input data contains no redundancy and is arranged with the most significant data first (in a sense, it is "big-endian"). The less these assumptions hold, the less we can truncate. Since many ML algorithms scale poorly with input size, we would prefer to eliminate the redundancy using a more aggressive algorithm, to keep the resulting feature size as low as possible.

## Dimension Reduction ##

A more sophisticated approach to the problem of reducing input size is to view it as a **dimension reduction** technique: our inputs can be modelled as points in high-dimensional spaces, which we want to project into a lower-dimensional space ($\left\{ {0, 1} \right\}^N$ in the case of $N$-bit vectors).

Truncation is a trivial dimension reduction technique: take the first $N$ coordinates (bits). More sophisticated projection functions consider the *distribution* of the points, and project with the hyperplane which preserves as much of the variance as possible (or, equivalently, reduces the **mutual information** between the points).

There are many techniques to find these hyperplanes, such as *Principle Component Analysis* and *auto-encoding*; however, since these techniques are effectively ML algorithms in their own right, they suffer some of the same constraints we're trying to avoid:

 - They operate *offline*, requiring all input points up-front
 - All input points must have the same dimensionality

In particular, the second constraint is precisely what we're trying to avoid. Sophisticated dimension reduction is still useful for *compressing* large, redundant features into smaller, information-dense representations, and as such provides a good complement to truncation.

The requirement for offline "batch" processing is more difficult to overcome, since any learning we perform for feature extraction will interfere with the core learning algorithm that's consuming these features. Such systems are possible, but out of scope for this small initial implementation.

## Structured Data ##

The task of dimension reduction changes when we consider *structured* data. Recursive structures, like trees and lists, have *fractal* dimension: adding layers to a recursive structure gives us more *fine-grained* features, rather than *orthogonal* features. For data mining context-free languages (eg. those of programming and theorem-proving systems), we will mainly be concerned with tree structures of the following form (where `FV`{.haskell} denotes a feature vector): `echo "" | pandoc -f markdown -t json`{pipe="cat > blank"} `chmod +x blank`{pipe="sh > /dev/null"}

```{.unwrap pipe="tee -a Trees.hs | ./blank"}
module Trees where

import Control.Applicative
import Test.QuickCheck
import Test.QuickCheck.Test

```

```{.haskell pipe="tee -a Trees.hs"}
data Tree = Leaf FV
          | Branch FV Tree Tree
```

```{.unwrap pipe="tee -a Trees.hs | ./blank"}

type FV = [Bool]

instance Arbitrary Tree where
  arbitrary = frequency [(2, Leaf   <$> arbitrary),
                         (1, Branch <$> arbitrary <*> arbitrary <*> arbitrary)]

instance Show Tree where
  show (Leaf   fv)     = "(L " ++ show fv ++ ")"
  show (Branch fv l r) = "(B " ++ show fv ++ " " ++ show l ++ " " ++ show r ++ ")"

qc p = do r <- quickCheckResult p
          if isSuccess r
             then return ()
             else error (show r)

```

### Truncation ###

Just like the non-recursive case, the simplest way to reduce our dimensionality is to truncate. To reduce an arbitrary `t :: Tree`{.haskell} to a maximum depth `d > 0`{.haskell}, we can use `reduceD d t`{.haskell} where

```{.haskell pipe="tee -a Trees.hs"}
reduceD 1 (Branch fv l r) = Leaf   fv
reduceD n (Leaf   fv)     = Leaf   fv
reduceD n (Branch fv l r) = Branch fv (reduceD (n-1) l)
                                      (reduceD (n-1) r)
```

```{.unwrap pipe="tee -a Trees.hs | ./blank"}

depth (Leaf   _)     = 1
depth (Branch _ l r) = 1 + max (depth l) (depth r)

reducesDepth t d = let d' = 1 + abs d
                    in depth (reduceD d' t) < (d' :: Int)

```

```{.unwrap pipe="runhaskell | ./blank"}
import Trees

main = qc reducesDepth
```

This is simple, but suffers two problems:

 - We must choose a conservatively large `d`{.haskell}, since we're throwing away information
 - The number of feature vectors grows exponentially as `d`{.haskell} increases

The first problem can't be avoided when truncating, but the second can be mitigated by truncating the *width* of the tree as well, to some `w > 0`{.haskell}. One way to truncate the width is tabulating the tree's feature vectors, then truncating the table to `w`{.haskell} $\times$ `d`{.haskell}. We can do this with `tabulate w d t`{.haskell}:

```{.haskell pipe="tee -a Trees.hs"}
tabulate w d t = take d (map (take w) (tabulate' t))

tabulate' (Leaf   fv)     = [fv] : []
tabulate' (Branch fv l r) = [fv] : merge (tabulate' l) (tabulate' r)

merge    []     ys  = ys
merge    xs     []  = xs
merge (x:xs) (y:ys) = (x ++ y) : merge xs ys
```

```{.unwrap pipe="tee -a Trees.hs | ./blank"}

mergeDim :: [[Bool]] -> [[Bool]] -> Bool
mergeDim xs ys = length (merge xs ys) == max (length xs) (length ys)

inRow n (Leaf   fv)     t = fv `elem` (t !! n)
inRow n (Branch fv l r) t = fv `elem` (t !! n) && inRow (n+1) l t &&
                                                  inRow (n+1) r t

haveRows t = inRow 0 t (tabulate' t)

```

```{.unwrap pipe="runhaskell | ./blank"}
import Trees

main = do qc mergeDim
          qc haveRows
```

#### Extracting Features from Haskell ####

The Glasgow Haskell Compiler provides a library interface to its operation, which we can use to parse Haskell code into tree structures. It also provides a *renaming* transformation, which makes all names unique; either by prefixing them with the name of the module which defines them, or by suffixing the name with a number.

### Linear Combinations ###

Rather than truncating our trees, we can *combine* the feature vectors of leaves into their parents, and hence *fold* the tree up to any finite depth. Following [@zanzotto2012distributed] we choose **circular convolution** (`cc`{.haskell}) as our combining function. Hence, to reduce `t :: Tree`{.haskell} to a single feature vector, we can use `reduceC t`{.haskell} where:

```{.haskell}
reduceC (Leaf fv)       = fv
reduceC (Branch fv l r) = cc fv (cc (reduceC l) (reduceC r))
```

We use circular convolution due to the following desirable properties:

 - **Non-commutative**: `cc a b`{.haskell} $\not\approx$ `cc b a`{.haskell}, hence we can distinguish between `Branch fv a b`{.haskell} and `Branch fv b a`{.haskell}
 - **Non-associative**: `cc a (cc b c)`{.haskell} $\not\approx$ `cc (cc a b) c`{.haskell}, hence we can distinguish between `Branch v1 a (Branch v2 b c)`{.haskell} and `Branch v1 (Branch v2 a b) c)`{.haskell}

Here we use $\not\approx$ to represent that these quantities differ *with high probability*, based on empirical testing. This is the best we can do, since the type of combining functions `(FV, FV) -> FV`{.haskell} has a co-domain strictly smaller than its domain, and hence it must discard some information. In the case of circular convolution, the remaining information is spread out among the bits in the resulting feature, which is known as a **distributed representation** [@plate1991holographic].

### Extracting Features from XML ###

This method of folding with circular convolution has been implemented in the Haskell program **Tree Features**, available at [https://gitorious.org/tree-features](https://gitorious.org/tree-features). The application parses arbitrary trees of XML and uses binary features, ie. feature vectors are bit vectors.

To calculate the initial feature of an XML element, before any folding occurs, we concatenate its name and attributes to produce a string `s`{.haskell}. The feature is then:

\begin{equation}
feature(n) = 2^{\md5(s) \pmod{L}}
\end{equation}

Where $\md5$ is the MD5 hash algorithm and $L$ is the length of the desired vector, given as a commandline argument. The result of $feature(s)$ is a bit vector of length $L$, containing only a single $1$. Due to the use of a hashing function, the position of that $1$ can be deterministically calculated from the input $s$, yet the *a priori* probability of each position is effectively uniform.

In other words, the hash introduces unwanted patterns which are *theoretically* learnable, but in practice a strong hash can be treated as irreversible and hence unlearnable.

#### Application to Coq ####

Prior to 2014-09-08, the Coq proof assistant provided a rudimentary XML import/export feature, which we can use to access tree structures for learning. We achieve this by using the `external`{.ocaml} primitive of the Ltac tactic language: `external "treefeatures" "32" t1 t2 t3.`{.ocaml} will generate an XML tree representing the Coq terms `t1`, `t2` and `t3`, and send it to the standard input of a `treefeatures` invocation, using a vector length argument of `32`.

Coq will also interpret the standard output of the command, to generate terms and tactics. This functionality isn't yet used by Tree Features, but it is clear that a feedback loop can be constructed, allowing for powerful ML approaches like **reinforcement learning**.

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

## Distributed Representations ##

TODO

## Sequencing ##

Any investigation of variable-size input would be incomplete without mentioning the *sequencing*. This is a lossless approach, which splits the input into fixed-size *chunks*, which are fed into an appropriate ML algorithm one at a time. The sequence is terminated by a sentinel; an "end-of-sequence" marker which, by construction, is distinguishable from the data chunks. This technique allows us to trade *space* (the size of our input) for *time* (the number of chunks in a sequence).

Not all ML algorithms can be adapted to accept sequences. One notable approach is to use **recurrent ANNs** (RANNs), which allow arbitrary connections between nodes, including cycles. Compared to **feed-forward** ANNs (FFANNs), which are acyclic, the *future output* of a RANN may depend arbitrarily on its *past inputs* (in fact, RANNs are universal computers).

The main problem with RANNs, compared to the more widely-used FFANNs, is the difficulty of training them. If we extend the standard backpropagation algorithm to handle cycles, we get the **backpropagation through time** algorithm [@werbos1990backpropagation]. However, this suffers a problem known as the **vanishing gradient**: error values decay exponentially as they propagate back through the cycles, which prevents effective learning of delayed dependencies, undermining the main advantage of RANNs. The vanishing gradient problem is the subject of current research, with countermeasures including **neuroevolution** (using evolutionary computation techniques to train an ANN) and **long short-term memory** (LSTM; introducing a few special, untrainable nodes to persist values for long time periods [@hochreiter1997long]).

# References #
