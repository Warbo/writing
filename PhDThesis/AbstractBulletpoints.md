# Points for Abstract

## Motivational

 - Software is becoming more important and more complex, hence so are aids to
   understanding it
 - Higher-level abstractions (e.g. pure functional programming) provide an
   opportunity to reason effectively about code, but it's under-exploited
 - Large corpora of software present an opportunity for machine learning and
   data mining
 - Unit testing is industry standard; property checking is becoming mainstream;
   property discovery is still an emerging area of research
 - Property discovery tools exist (e.g. QuickSpec, Speculate), but brute-force
   requires carefully selected inputs, and their output isn't quantified
 - Opportunity to quantify and compare performance
 - Opportunity to improve/automate the selection process, using machine learning
   (similar task to premise selection/relevance filtering/similarity clustering)
 - Mathematical calculation is automated; theorem proving is increasingly so;
   relatively little progress on automating conjecture generation (question
   asking rather than answering)

## Contributions

 - Generic benchmarking methodology for property discovery/conjecture generation
 - Benchmarking and direct comparison of QuickSpec 1 and IsaCoSy
 - End-to-end automation for property discovery
 - Runtime evaluation of Haskell code with dynamic dependencies
 - Framework for automated selection of property discovery/conjecture generation
   inputs ("signature selection")
 - Implementation of "recurrent clustering" for arbitrary tree structures
   (including application to Haskell Core ASTs)
 - Implementation of circular convolution for arbitrary tree structures
 - Experimental analysis of signature selection via recurrent clustering,
   compared to a (pseudo-)randomised control.

## Future Directions

 - Automated generation of high-level peephole optimisation (via profiling)
 - Abstraction/interface/concept discovery by data mining properties (e.g. via
   anti-unification)
 - On-the-fly input selection, rather than up-front signature selection + brute
   force
 - Representation learning (e.g. adversarial networks, posing/proving)
 - Integrating types into the reasoning (not sure quite how yet; other than just
   annotating the trees with extra nodes).

# "Narrative" options

 - Focus on the mathematical side: conjecture generation, theorem proving, etc.
   with applications to automated reasoning, and in particular (due to CUrry
   Howard) software verification.

 - Focus on the programming language theory side: property discovery, with
   overlaps (due to Curry Howard) with mathematical modelling, theorem proving,
   etc.

Personally, I feel more familiar/comfortable with framing things from the
software side. Whilst potentially narrower in scope, it's much more concrete and
easier (for me) to justify and motivate. It also meshes with my own background,
motivations and networks (e.g. across Scotland and elsewhere).

Framing things in terms of the mathematics gives me less confidence, as I don't
want to be yet another AI researcher telling mathematicians how to do their job
;)
