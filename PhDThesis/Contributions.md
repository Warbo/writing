# Possible Contributions

 In roughly decreasing order of significance:

 - Conjecture/property generation benchmarking methodology
 - Theory Exploration Benchmark, using TIP
 - Empirical benchmarking and comparison of QuickSpec and IsaCoSy
 - Identification of the input selection problem for conjecture/property
   generation (AKA "signature selection")
 - Empirical analysis of recurrent clustering for signature selection, compared
   to a (pseudo-)random control and non-learning approach (circular
   convolution).
 - Recurrent clustering application to arbitrary tree structures (which we
   apply to Haskell Core)

The following are mostly implementation/engineering details, but might have some
merit:

 - End-to-end QuickSpec runner (haskell-te)
 - End-to-end Isabelle/IsaPlanner/IsaCoSy runner (isaplanner-tip)
 - Runtime Haskell evaluation with dynamic dependencies (nix-eval)
 - General purpose Haskell source code extraction (AstPlugin; now made obsolete
   by GHC "source plugins")
 - Reproducible experimental environments (using Nix; not really "new")
 - General benchmarking framework (asv-nix; tiny addition to existing work)
