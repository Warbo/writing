# Trip Report: CICM 2017 #

Most of the research presented at CICM fell into the following broad themes:

 - Standards for system interoperability; in particular OpenMath and Semantic
   LaTeX, and tools/infrastructure for discovering/converting/manipulating
   these.
 - New UIs for existing tools.
 - New formal systems/frameworks.

## Interoperability ##

Part of this effort comes from two EU projects designed to improve
interoperability between Free Software projects for mathematics.

OpenDreamKit aims to combine existing FOSS math tools, such as GAP (a language
specialising in group theory), Sage (a Python frontend for accessing and
combining many computer algebra and scientific/numerical computing systems) and
Jupyter (a browser-based "interactive notebook" UI).

### OpenMath ###

OpenDreamKit seems to have embraced OpenMath as a standard for interoperability,
with an approach dubbed "Math in the Middle". In this approach, rather than
hard-coding O(n^2) interfaces between systems (e.g. GAP to Sage, Sage to GAP,
Maxima to Sage, GAP to Maxima, etc.), instead we treat 'maths itself' as a
standard, by giving formal descriptions (at various levels of detail) of each
system, so that automated reasoning systems can do the work of translating. An
RPC mechanism called SCSCP has also been formalised, as a way to send OpenMath
data and invoke commands over the network.

The MMT ("meta-meta-theory") framework has been used to do this formalisation,
due to its flexibility (e.g. there's a choice of underlying logic, proofs are
optional, etc.)

One criticism of OpenMath is the amount of effort required to specify a "content
dictionary", describing what particular mathematical objects are. A more
lightweight approach is Math Object Identifiers, which are similar in spirit to
DOIs but for mathematical objects (e.g. functions, proofs, etc.). These are used
on MathHub.info, for example.

Regarding potential uses of OpenMath and its infrastructure, since it's designed
as an interchange format it may be useful for plugging into existing tools.
HipSpec already plugs QuickSpec into external tools (e.g. Z3 and CVC4); maybe
there's scope for plugging into more tools, for verification and exploration?

Making theory exploration tools accessible to others, via a standard i/o format
may be beneficial too. We currently allow input in the form of TIP, and in the
form of Haskell; we output a simple JSON encoding of equations. As a minimum, we
could output an OpenMath encoding. In fact, our `reduce-equations` tool, which
simplifies a given set of equations by removing redundancies, could be augmented
to allow OpenMath i/o; there are existing OpenMath representations and parsers/
pretty-printers for Haskell available on Hackage. Since all of our conjectures
are equations, with expressions composed of variables, constants and function
application, that's the only part of OpenMath we need to use.

More elaborately, we could relate the functions we're given (as GHC Core ASTs)
to known mathematical objects, like addition, multiplication, etc. This seems
like quite a lot of effort, so maybe avoid it for now.

### SMT-LIB ###

The other EU project mentioned is SC^2, which aims to combine tools for
satisfiability (e.g. SMT solvers like Z3) with tools for symbolic computation
(e.g. computer algebra systems).

During the OpenMath workshop, James Davenport presented an overview of the
SMT-LIB format used by SMT solvers, its incompatibilities with OpenMath, and how
both formats could be improved and brought closer together.

This was interesting for two reasons: SMT solvers are widely used as backends
for automated theorem proving (e.g. Isabelle's SledgeHammer and Haskell's
HipSpec); and the SMT-LIB format is used as the basis for the TIP format (TIP is
to HOL as SMT-LIB is to FOL).

One interesting issue is that SMT-LIB requires that syntactically-distinct
expressions in a model must be semantically-distinct values in the theory. For
example, we can't encode the integers in a way that gives distinct +0 and -0,
since those will be considered different values, and hence our theory won't
behave the same as the integers. This is apparently a problem when attempting to
encode theories like the algebraic real numbers, since there must only be one
possible encoding/representation for each number.

### Semantic LaTeX ###

Semantic LaTeX is a collection of LaTeX macros for marking up particular objects
in mathematical formulae, rather than focusing on just the presentation. A
running example was "Jacobi polynomials", which are typically written as `P`
with a bunch of subscripts and superscripts, which isn't particularly machine
readable; instead, we can use a LaTeX macro to specify that we want a Jacobi
polynomial, with various parameters, and it will be rendered as normal, but
*also* be usable by other software.

As an example, each Semantic LaTeX macro has an entry in the Digital Library of
Mathematical Functions, which is curated by NIST in the US. Translations into
computer algebra systems are included in the database, so that the LaTeX source
can be re-used without having to maintain two versions of every formula.

Projects were also proposed to use machine learning methods (e.g. from natural
language processing) to try and infer the semantics of regular LaTeX, and
perform automatic conversion if possible.

In a similar vein, the "metaTeX" project was described, which is an attempt to
infer a "truthiness"/probability for TeX formulas. This still seems to be at the
idea stage, but a general-purpose machine learning approach to this problem
would be *very* useful in a variety of contexts; for example, guiding search
towards more likely lemmas/conjectures/etc. or for a "query by committee"
approach to deciding interestingness.

## New UIs/Tools ##

### ML4PG ###

Katya presented ML4PG, with the focus on its combination of existing machine
learning programs and interactive theorem provers (namely Coq). Previously
published work on ML4PG focused on data mining tactics, written in Coq's Ltac
language. This proved to be less informative than the proof terms themselves,
which this work focused on. The emphasis was on the conversion of dependently-
typed expressions into vectors via recurrent clustering, and how that manages to
make semantically meaningful distinctions. The example being uses of the `foldl`
function, where some uses appeared in one cluster and others occurred elsewhere,
when there are no syntactic differences between the expressions. This is because
the names being used had already been clustered, and some were deemed similar
(e.g. a summing function and a list concatenation function), whilst the others
were significantly different.

A variant of this algorithm is the one used in MLSpec for Haskell; although the
Haskell version doesn't have access to the types, and doesn't use the centrality
information from the clusters.

### ENIGMA ###

Another supervised learning system from Josef Urban et al. for premise selection
and re-proving in first-order ATP systems (E and Vampire).

The most interesting aspect is how expression trees are represented as inputs to
the machine learning system (e.g. like the tree-flattening done by ML4PG). In
this case, AST nodes for variables and skolem constants are replaced with
special symbols, since they don't occur in the signature. The resulting tree is
then traversed to find all paths containing three nodes. For example, take the
following AST:

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

We replacing variables (`x`), and skolem constants (none in this AST), to get:

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

The "`equal`, `plus`, `*`" path appears twice, so it has value 2; the rest
appear once so they have value 1. All other possible paths for the theory's
signature have value 0. These are all put into a massive (sparse) vector, and
used as training data for supervised learning.

The downsides to this approach are that the trees are encoded in a rather
indirect way, so the impact of their structure on the expression (e.g. by
including a `not`) may be difficult to learn; and the size of the vectors grows
exponentially with the signature size, since it's including all combinations.
Even with sparse vectors, this seems inefficient.

### WebLurch ###

A "Mathematical word processor", available at nathancarter.github.io/webluch

This is a nice browser-based WYSIWYG document editor, based on TinyMCE, which
allows literate programming. Semantically-meaningful expressions are put into
text-boxes, which can be arranged arbitrarily among the prose on a page. The
content of these boxes can be marked up as an AST, and sent to a variety of
"backends" to be manipulated in arbitrary ways. Some examples demonstrated were
formal proofs sent into Lean, programs which were pretty-printed to Python and
Javascript, and OpenMath "content dictionary" documents.

Some nice features are that it's all client-side Javascript, so no server
backend is needed (although it's not usable from `file://` due to 3rd-party
scripts; it can be run from a local static file server, or IPFS). It also has no
separate database; all data is stored in the HTML document, and parsed out by
the Javascript, so it should be easily shareable, versionable, etc.

### Theory Diagrams ###

Many "theory diagrams" were shown, mostly modelled with MMT and OpenMath. One
particularly interesting use was generating "model pathway diagrams" to
represent quantities and laws in a physical theory (the example being
semiconductor physics).

These might be a nice way to present anything with a "value level" and a "law
level", such as typeclasses or interfaces.

## New Formal Systems/Frameworks ##

### LF ###

LF is one of the logical frameworks used by MMT. It's a dependently-typed λ
calculus, which may be easier to programmatically manipulate than e.g. Coq's
Calculus of Constructions, or GHC Core. Useful to keep in mind, alongside
alternatives like Idris's "TT" language, or Gabriel Gonzalez's languages like
Dhall and Morte.

### MathScheme ###

An approach to integrating computer algebra systems with ATP/ITP. The idea is to
use "biform theories", which include include symbols, expressions (ASTs),
"transformers" and axioms. The axioms allow "algebraic" reasoning (e.g. computer
algebra systems), whilst the ASTs allow "algorithmic" reasoning (e.g. automated
or interactive theorem proving, and computation).

One particularly nice approach was the embedding of quotation and evaluation in
a logic. The description is that we can quote (some) logical terms into a
representation of their syntax, run some algorithms on that syntax (e.g. to
convert into a normal form), and re-evaluate the result in the logic:

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

The tricky part seems to be getting this "global" quotation/evaluation to be
consistent; there are existing "local" approaches, e.g. in Agda, but they're
less amenable to this algebraic/algorithmic split, because new syntax
representations need to be written manually every time.

### Theory Repair ###

Alan Bundy's talk was about how to automatically "repair" a theory which doesn't
work in the way it should. An example is a robot, with some internal model of
the world, which either observes something that its model forbids, or predicts
things which cannot happen.

The running example uses unification in resolution proofs in first-order logic,
but the idea should be extendable to other systems, with some work. The main
point is that if we can prove something we don't want, we should change the
theory to make the unifications used in that proof fail. Dually, if we can't
prove something we do want, we should change the theory to make the failing
unifications succeed.

For example:

    Mother(Diana,   Harry)
    Mother(Camilla, Harry)
    Mother(x, z) ^ Mother(y, z) -> x = y

This theory gives a few concrete facts, along with the general statement that
people only have one mother. This is faulty, since it lets us prove
`Diana = Camilla`, which we don't want. We can break the unifications that lead
to this in many ways; one way is to split the `Mother` predicate into two:

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
the extra argument approach to retain the connection, instead of having to
re-discover it.

One way to mitigate some of the search space problem would be to automatically
generate an experiment: if some property is "measurable", and we have many
potential ways to repair our theory, we could make create several theories, each
with a different repair, and compare the "measurable" quantities we can derive
from them: if there is disagreement, we have an empirical way to determine which
is "better".
