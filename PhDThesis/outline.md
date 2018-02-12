Title: Use of "Interestingness" in Scaling Automated Mathematical Discovery

What we need to include:

 - History of automated mathematical discovery
 - History of what counts as "interesting"

Empirical proposal for measuring what is "interesting" (TEBenchmark)

Evaluation and comparison of existing systems using this benchmark (QuickSpec v1
and IsaCoSy)

Application of machine learning to focus existing systems on what is "interesting"

 - Overview of machine learning techniques:
  - Supervised vs unsupervised
  - Clustering
  - Representing structured inputs
 - Bucketing algorithm
  - Use with pseudorandom similarity metric
  - Use with "flattened tree" similarity metric
  - Potentially some other comparison?

Practical uses of automated mathematical discovery systems

 - Optimisation
  - Self-optimising programs
  - Use with Hutter search?
 - Finding abstractions (anti-unification)
  - Concept formation?

Application of discovery system to existing software packages

 - Packages from Hackage (may need extra Arbitrary instances)
 - GHC libraries (base, maybe more)
 - Maybe use test suites as ground truth?

Conclusions


---

We have a few things sat around gathering dust. Can we fit them in somewhere?

 - Purely-functional self-modifying code. This could be an implementation
   vehicle for open-ended self-optimising code.

 - Powerplay. This uses self-invented problems. Could we use "interesting"
   conjectures from a theory exploration system to guide the self-improvement of
   an automated theorem prover?

Things which have influenced my thinking, which would be nice to include:

 - Interestingness based on compression progress. The "compression" could
   perhaps come from writing proof tactics? For example, try to prove any given
   conjecture using a single 'prove' tactic. Given a (conjecture, tactic) pair,
   and an existing tactic, we deem the conjecture to be "interesting" if it
   can't be proved by the existing tactic, it can be proved by the new tactic,
   and the new tactic is smaller than the old tactic. Hmm... This wouldn't allow
   tactics to increase in size. The compression progress idea relies on a
   lossless compression of all 'past experience', which in this situation would
   just be a list of all conjectures we've tried. This just passes the buck on
   what's "interesting", since those conjectures need to be chosen somehow...

 - Artificial curiosity systems, like problem generators rewarded by the
   variance of how difficult a population of solvers found the problem to be.

 - Recursive self-improvement: take an algorithm which searches for improvements
   to itself, and run it for a few self-improvement iterations. How do the
   improvements to the search algorithm compare against the difficulty of
   improving an optimised system ('recalcitrance')?

 - Can we create a compiler by providing a property discovery algorithm with a
   specification and an model interpreter (e.g. for x86 machine code)?

 - A result I'd really like to have is a system which collapses down abstraction
   layers. This would be especially nice if it worked across languages, and we
   could either use staged execution/compilation and/or a database of
   compiled/transformed code.
