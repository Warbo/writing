# Trip Report: CICM 2017 #

Most of the research presented at CICM fell into the following broad themes:

 - Standards for system interoperability; in particular OpenMath and Semantic
   LaTeX, tools/infrastructure for discovering/converting/manipulating these, as
   well as a couple of EU projects with this goal (OpenDreamKit and SC^2).
 - New UIs, mostly for existing systems, e.g. MathHub.info

## Raw Notes ##

OpenDreamKit: EU project to combine FOSS math tools (GAP, Sage, Jupyter, etc.)

SCSCP: Protocol for symbolic algebra systems
 - Eh, just bog standard RPC :(

MMT:
 - Meta-meta-theory
 - Describe things in a formal system, proofs are optional, etc.

"Math in the Middle":
 - Rather than hard-coding interfaces between systems (e.g. a GAP plugin for
   Sage), try to make a formal mathematical description of what an APIs is/does.
 - Use reasoning tools on these formal descriptions, e.g. to derive conversions,
   etc.

Useful for describing things in a high-level way (hand-waving over the
specifics, and hence remaining more generally applicable); as well as drilling
down into details of how things are implemented in some particular system. Also
allows choice of logic (e.g. Coq-compatible, etc.)

How might these be useful for discovering, exploring, etc.? One idea is if we
want to call out to external tools, e.g. as a portfolio, it can be useful to
have a common tongue.

Also useful to have a high-level format to represent ideas, which we may find
instances of (e.g. groups, which may be out there in Maths land, but might not
be an e.g. typeclass, etc.)

SC^2:
 - EU project to combine satisfiability (e.g. SMT) and symbolic computation.

SMT-LIB issue - models may be "larger" than the problem. Example:

  ∃x. x^2 = 2

This definition only involves ℕ, but therea re no models/solutions in ℕ. There
*are* solutions in ℝ, i.e. {±⎷2}, but how do we represent them?

SMT(-LIB) requires syntactically-distinct expressions/values to be different
values, i.e. they must all be canonical (for example, if a representation of ℤ
has distinct constructions for +0 and -0, then as far as SMT(-LIB) is concerned,
these are different values.

This makes it hard to represent (algebraic) reals, which would be useful for the
above example, since choosing primitive constructors such that no distinct
combinations correspond to the same number is very hard.

MOI:
 - Math Object Identifier
 - Similar in spirit to DOI
 - Used on MathHub.info

There are Python bindings for OpenMath, made for GAP as part of OpenDreamKit

Would OpenMath be useful for our purposes? All of our conjectures are of the
form:

    {"relation": "~=",
     "lhs": ...,
     "rhs": ...}

We could look up "content dictionaries" for:

 - Conjectures (i.e. may/may not be true)
 - Universal quantifiers
 - Function application

We could also model GHCCore as a content dictionary. Haskell names are interesting, as they can be canonical, etc. Language should be versioned too!

Maybe we could write a GHC.Core interpreter? What about a type inference algorithm? Meh, not yet :)

What about Idris TT? Screw it, this isn't productive!

Maybe nice to have a JSON -> OpenMath layer on our output.

reduce-equations might benefit from having an OpenMath reader/writer, since it's
currently hard-coded to our own ad-hoc format.

What if we rename to, say, IPFS hashes? Given output from GHC AstPlugin, insert
each into IPFS as, say, GHC Core ASTs. Use the hash as the "canonical" name,
which we can look up (if wanted) via IPFS. Problem is mutual recursion; we'd
have to add such definitions together. We don't want spurious hash changes, so
we'd have to add *only* those mutually-recursive defs in a set together,
etc. Look at IP Linked Data: maybe not worth translating into (i.e. keep strings
of Core), but maybe it can help us handle mutual recursion. What if we
parameterise?

    x = (foo (bar baz) bar)

                ||
                \/

    x = (0   (1   2  ) 1  )

This is similar to using de Bruijn indices for names. We then instantiate:

    (apply x foo bar baz)

Does this help us? Still references names :/

LF:
 - Dependently-types λ calculus. Maybe easier to programmatically manipulate
   than e.g. Co(I)C (Calculus of ((Co-)Inductive) Constructions)

DLMF:
 - Digital library of Mathematical functions

Semantic LaTeX:
 - Unreleased?

MathScheme:
 - Integrate computer algebra systems with ATP/ITP

Biform theories:
 - Theories include symbols, expressions (ASTs), "transformers" and axioms
 - The axioms allow "algebraic" reasoning (CAS)
 - ASTs allow "algorithmic" reasoning.

metaTeX:
 - Learn to assign a "truthiness"/probability to TeX sentences.

SOAR(?) Computational analogy ("cat" and "car" example)

Quotation and evaluation:

    +----------------------------+
    | Language                   |
    |                            |
    |  +-----------------------+ | quote +----------------+
    |  | Representable objects |-------->| Syntax objects |
    |  |                       | |       |                |
    |  |                       | | eval  |                |
    |  |                       |<--------|                |
    |  +-----------------------+ |       +----------------+
    |                            |
    +----------------------------+

In a system with reflection, syntax objects are part of the language:

    +--------------------------------------------------------+
    | Language                                               |
    |                                                        |
    |  +-----------------------+  quote  +----------------+  |
    |  | Representable objects |-------->| Syntax objects |  |
    |  |                       |         |                |  |
    |  |                       |  eval   |                |  |
    |  |                       |<--------|                |  |
    |  +-----------------------+         +----------------+  |
    |                                                        |
    +--------------------------------------------------------+

Theory diagrams:
 - Model pathway diagrams to represent quantities and laws
 - Could these be used to present typeclasses/interfaces?

ENIGMA:
 - Josef Urban et al.
 - Premise selection, etc. for E, Vampire, etc.
 - Replace AST nodes of variables with a single symbol
 - Replace skolem constants with another (single) symbol
 - Count all paths of three nodes

For example, take the following AST:

                        +-- x
                        |
            +-- plus ---+
            |           |
            |           +-- x
    equal --+
            |           +-- x
            |           |
            +-- times --+
                        |
                        +-- succ -- succ -- zero

Replacing variables (`x`), and skolem constants (none in this AST), we get:

                        +-- *
                        |
            +-- plus ---+
            |           |
            |           +-- *
    equal --+
            |           +-- *
            |           |
            +-- times --+
                        |
                        +-- succ -- succ -- zero


The paths containing 3 nodes are:

 - `equal`, `plus`, `*`
 - `equal`, `plus`, `*`
 - `equal`, `times`, `*`
 - `equal`, `times`, `succ`
 - `times`, `succ`, `succ`
 - `succ`, `succ`, `zero`

The "`equal`, `plus`, `*`" path appears twice, so it has value 2; the rest have
value 1. All other possible paths for the theory's signature have value 0. These
are all put into a massive (sparse) vector, and used as training data for
supervised learning.

ATP: disjunction of formulas; proof by contradiction (e.g. SLD resolution)
succeeds when we get an empty set of formulas/clauses.

This is because disjunction of no formulae is trivially false, and hence a
contradiction.

Think `any someList`, which is false if `someList` is empty (whilst
`all someList` would be true).

WebLurch:
 - nathancarter.github.io/webluch
 - "Mathematical word processor"
 - WYSIWYG document editor
 - Allows literate programming:
  - Text-boxes for semantically-meaningful expressions
  - Content of these boxes can be marked up as an AST
  - "Backend" can manipulate these in arbitrary ways
   - Stitching together formal proofs and checking them
   - Spitting out valid Python and/or Javascript code, and running it
 - No separate database; all data is stored in the HTML document.
 - Whole "application" is client-side Javascript; no server.
 - Not usable from `file://` due to 3rd-party scripts, but can run from IPFS

VMEXT:
 - Attempt to unify many redundant tree formats for expressions
 - Allows semantic info

Theory repair:
 - Example is unification in resolution proofs in first-order logic
 - Should be extendable to other systems, with some work
 - If we can prove something we don't want, change the theory to make such
   unification fail
 - If we can't prove something we do want, change the theory to make the failing
   unification succeed

For example:

    Mother(Diana,   Harry)
    Mother(Camilla, Harry)
    Mother(x, z) ^ Mother(y, z) -> x = y

This lets us prove `Diana = Camilla`, which we don't want. We can break the
unification in many ways; one way is to split the `Mother` predicate into two:

    Mother(Diana,    Harry)
    Mother'(Camilla, Harry)
    Mother(x, z) ^ Mother(y, z) -> x = y

This doesn't let us derive `Diana = Camilla`, since `Camilla` isn't a `Mother`,
she's a `Mother'`. Intuitively, we can interpret `Mother'` as being
"step-mother".

The problem with this approach is that the search space is huge: there are many
ways to make unification fail. Another way would be to introduce an extra
argument to `Mother`:

    Mother(Diana,   Harry, Birth)
    Mother(Camilla, Harry, Step)
    Mother(x, z, Birth) ^ Mother(y, z, Birth) -> x = y

The advantage of using an extra argument is that we can still reason about
"motherness" in general, by using a variable for the final argument. In the case
of separate `Mother` and `StepMother` predicates, we might want an extra
`Motherlike` predicate to capture more general properties which apply to both:

        Mother(x, y) -> Motherlike(x, y)
    StepMother(x, y) -> Motherlike(x, y)

This could be found via anti-unification, for example, but we might as well use
the extra argument approach.

One way to mitigate some of the search space problem would be to automatically
generate an experiment: if some property is "measurable", and we have many
potential ways to repair our theory, we could make create several theories, each
with a different repair, and sompare the "measurable" quantities we can derive
from them: if there is disagreement, we have an empirical way to determine which
is "better".
