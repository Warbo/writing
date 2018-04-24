# Quantitative Benchmarking for Conjecture Generation #

# Background: Formal Systems #

 - Foundation for mathematics
 - Human maths is less formal, but formalisable in principle
 - Essential for most automated reasoning techniques (theorem proving,
   counterexample finding, model checking, ...)
 - Essentially the same (by Curry-Howard correspondence) as computer programming
 - Programming more relatable for CS, stick to it for examples
 - Formal methods achievements and effort required: CompCert, AMD FPU, SEL4

# Background: Motivating Example #

(Maybe live-code in Agda?)

 - Singly-linked lists (nil and cons)
 - Append, map, reduce
 - Show data-dependency of reduce
  - Explain why that's bad for parallelism
 - Ask if map has a data dependency
 - Prove that elements are independent (append commutes)
  - Proceed as normal, showing that we need some lemmas (e.g. append x Nil = x)
  - Explain why this independence is good for parallelism
