This scaling issue can be tackled in several ways; here we choose to keep the theory exploration framework unchanged, and instead consider methods to automate the "theory selection" task: that careful choosing of components to study. This is similar to the *premise selection* task in automated theorem proving, as both must compute some approximate "relevance" measure across a large space of symbolic structures. Yet the differences are significant: premise selection has a pre-specified target to compare against, which theory selection lacks; similary, premise selection is associated with a definite fitness criterion (the success or failure of the subsequent proof attempt), whilst "success" is not so clear in theory exploration.

These underspecified, approximate criteria make theory selection a clear candidate for machine learning techniques.

# Machine Learning #

Machine learning, defined by Alpaydin[alpaydin2014introduction] as "programming computers to optimize a performance criterion using example data or past experience", is an increasingly popular discipline for tackling problems which lack a clear algorithmic treatment. A classic example is spam filters, which can be inferred via straightforward statistical methods[graham2002plan] despite the complexity and subtlety of the emails being classified.

## Evaluating Performance ##

From this definition, it is clear that we must choose some performance criterion and some example data. The performance of our selection process depends on the performance of the subsequent exploration phase, which in turn should include factors such as the number of properties discovered, the time taken and the information content of those properties.



# Methodology #

We have built a tool called ML4HS (Machine Learning for Haskell). This modular framework performs several tasks:

 - Extracting syntax trees from Haskell packages, using a custom plugin for the Glasgow Haskell Compiler (GHC).
 - Discarding definitions which <span style="font-variant:small-caps;">QuickSpec</span> does not accept.
 - Performing feature extraction and clustering of the remaining definitions.
 - Constructing <span style="font-variant:small-caps;">QuickSpec</span> theories and invoking their exploration.

We use the ML4HS framework for all experiments; the machine learning phases are optional, so we ignore them when benchmarking <span style="font-variant:small-caps;">QuickSpec</span> on its own. We use version 4.8 of the Haskell `base` library as our input, since it is widely used and very large, and thus an attractive target for library authors to explore in conjunction with their own packages.

First we measure <span style="font-variant:small-caps;">QuickSpec</span>'s performance without any clustering, in order to determine the effect of theory size and search depth on performance. We generate smaller approximations of the `base` package in three ways: `base-uniform-N` discards definitions uniformly across the modules, until it contains `N` definitions; `base-good-N` preferentially discards definitions which appear in the fewest equations; `base-bad-N` preferentially discards definitions appearing in the most equations. We can expect real libraries of size `N` to perform somewhere between `base-good-N` and `base-bad-N`.

Performance is measured as the average rate of equation discovery $\overline R_e = {N_e \over T}$, where $N_e$ is the total number of equations discovered and $T$ is the total time taken. We must use averages, since <span style="font-variant:small-caps;">QuickSpec</span> operates in stages: producing a large number of "raw" equations, then removing redundancies.

We use these benchmarks to determine effective parameter values for our machine learning experiments, which use a k-means clustering algorithm consist of a randomised clustering algorithm

# Results #

# Conclusion and Future Work #
