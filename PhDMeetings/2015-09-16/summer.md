---
bibliography: Bibtex.bib
---

## Theory Exploration System

A lot of my time over summer was spent on improving/fixing the wrapper around QuickSpec which I've dubbed "ML4HS". Whilst theoretically straightforward, peculiarities of Haskell and its infrastructure (GHC, Cabal, etc.) has lead to several difficulties when trying to build QuickSpec signatures. The common theme is that it would be useful to have a function like `eval :: [PackageName] -> [ModuleName] -> Expr -> IO (Maybe Expr)`{.haskell} to (attempt to) evaluate Haskell code in the context of other packages and modules. This way, we could simply ignore values which lead to errors. Until someone implements such a thing, our QuickSpec integration is instead rather fragile: we must identify and remove any potentially troublesome values long before they reach QuickSpec, since most of the errors we encounter are unrecoverable:

 - Syntax errors. These can occur when extracting functions from Core, since implicit values like type parameters and typeclass dictionaries are reified to values with invalid Haskell names (eg. `$c<` for an implementation of `<`{.haskell})
 - Type errors. These can occur when we try to add functions to a signature which do not implement the required typeclasses (`Ord`{.haskell} and `Typeable`{.haskell}).
 - Scope errors. These can occur if we try to use values which are not exported.
 - GHC panics. These can occur due to mishandling of GHC's API.
 - All of the above, at the Template Haskell level (which we use for monomorphising)

Here is a high-level overview of the project:

```{pipe="cat > d1.dit"}
     /-------\
     |Hackage|
     \-------/
         |
         V
   +----------+
   |AST Plugin|
   +----------+
         |    /----\
         |    |    |
         V    V    |
   +------------+  |
   |AST database|  | annotate
   +------------+  |
         |    |    |
         V    \----/
   +------------+
   |Monomorphise|
   +------------+
         |
         V
 +-----------------+
 |Theory definition|
 +-----------------+
         |
         V
+------------------+
|Theory exploration|
+------------------+
```

```{pipe="cat > file2img.sh"}
#!/bin/sh
DATA=$(base64 -w 0)
echo "<img alt='$1' src='data:image/png;base64,$DATA' />"
```

```{.unwrap pipe="sh | pandoc -t json"}
chmod +x file2img.sh > /dev/null
ditaa d1.dit d1.png >> /dev/stderr
./file2img.sh "ML4HS" < d1.png
```

 - Haskell infrastructure
    - Ouanis
     - getDeps
      - Appends a "dependencies" annotation to an array of ASTs
     - order-deps
      - Topologically sort ASTs based on dependencies
    - Me
     - ML4HSFE
      - ML4PG-style feature extraction for Haskell
      - Turn ASTs into matrices, look up values for each cell
     - ML4HS
     - HS2AST
     - MLSpec
     - AstPlugin
      -
     - ArbitraryHaskell

## Reading

Over the summer I've read many papers, mostly in machine learning, to better understand the landscape of approaches, their relationships, history and the current state of the art.

I've also started following Andrew Ng's machine learning lectures from Stanford.

I've particularly focused on k-means and associated algorithms, specifically to understand the following:

 - How repeatable are its results? [@bottou1994convergence]
 - How to choose parameters, eg. the number of clusters [@pelleg2000x] and their initial locations [@arthur2007k]?
 - How to ensure scalability/tractability? [@bahmani2012scalable]

I've also kept a few questions in mind regarding recurrent clustering (RC):

 - Can we guarantee convergence of RC?
 - How repeatable/replicable is RC (eg. do results vary widely based on initial conditions)?
 - How does RC compare with in-lining of definitions?

As well as AI/ML methods, I've also looked into their application to Mathematics. From early theorem provers like , to exploratory applications in universal algebra[@spector2008genetic]. and  Other reading has been ad-hoc, along the lines of either following citation chains or proceedings One source I've been working my way through is the [Journal of Machine Learning Research](http://www.jmlr.org/)

###

    - Machine learning
     - [@pelleg2000x]
     - [@arthur2007k]
     - [@spector2008genetic]
    - PLT
     - [@kiselyov2015freer]

## References
