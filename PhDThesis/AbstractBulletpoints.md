# Points for Abstract

## Motivational

 - Software is becoming more important and more complex, hence so are aids to
   understanding it
 - Higher-level abstractions (e.g. pure functional programming) provide an
   opportunity to reason effectively about code, but it's under-exploited
 - Large corpora of software present an opportunity for machine learning and
   data mining
 - Unit testing is industry standard; property checking is becoming mainstream;
   property discovery is an emerging area of research
 - Property discovery tools exist (e.g. QuickSpec, Speculate), but brute-force
   requires carefully selected inputs and output isn't quantified
 - Opportunity to quantify and compare performance
 - Opportunity to improve/automate the selection process, using machine learning
   (similar to premise selection/relevance filtering/similarity clustering)
 - Mathematical calculations are mostly automated; theorem proving is
   increasingly automated; relatively little attention has been given to
   automating conjecture generation (question asking rather than answering)

## Contributions

 - Generic benchmarking methodology for property discovery/conjecture generation
 - Benchmarking and direct comparison of QuickSpec 1 and IsaCoSy
 - End-to-end automation for property discovery
 - Runtime evaluation of Haskell code with dynamic dependencies
 - Framework for automated selection of property discovery/conjecture generation
   inputs ("bucketing")
 - Implementation of "recurrent clustering" for arbitrary tree structures
   (including application to Haskell Core ASTs)
 - Implementation of circular convolution for arbitrary tree structures
 - Experimental analysis of bucketing via recurrent clustering, compared to a
   (pseudo-)randomised control.

## Future Directions

 - Automated generation of high-level peephole optimisation (via profiling)
 - Abstraction/interface/concept discovery by data mining properties (e.g. via
   anti-unification)
 - On-the-fly input selection, rather than up-front bucketing + brute force
 - Representation learning (e.g. adversarial networks, posing/proving)
