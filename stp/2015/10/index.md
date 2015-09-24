---
title: Scottish Theorem Proving
header-includes: |
  <link type="text/css" rel="stylesheet" href="http://fonts.googleapis.com/css?family=Francois+One&ver=4.0" />
  <link href="favicon.ico" rel="shortcut icon">
  <style type="text/css">
    h1 {
      color: #e84747;
      font-family: "Francois One",Tahoma,Verdana,Arial,Sans-Serif;
      font-size: 2.5em;
      font-weight: bold;
      margin-bottom: 0px;
    }
    html {
      background-color: #e5e5e5;
    }
    body {
      background-color: #ffffff;
      background-repeat: no-repeat;
      color: #000000;
      font-family: Sans-Serif;
      height: 100%;
      margin: 0px 4%;
      padding: 5px;
      position: relative;
      text-shadow: 0px 0px 3px #ffffff;
    }
    #logos {
      float: right;
    }
    #logos img {
      max-width: 250px;
      max-height: 200px;
      margin: 10px;
    }
    #subtitle {
      margin-bottom: 2em;
    }
    #subtitle p {
      margin: 0px;
    }
    #header {
      display: none;
    }
  </style>
---
<div id="logos">
  <a href="http://www.dundee.ac.uk">
   <img id="dundee" src="dundee_logo.png"
        alt="University of Dundee" />
  </a>
  <br />
  <a href="http://www.sicsa.ac.uk">
   <img id="sicsa"  src="sicsa.jpg"
        alt="Scottish Informatics and Computer Science Alliance" />
  </a>
  <br />
  <a href="https://www.epsrc.ac.uk">
   <img id="epsrc"  src="epsrc.jpg"
        alt="Engineering and Physical Sciences Research Council" />
  </a>
</div>

# Scottish Theorem Proving

<div id="subtitle">

7th October 2015, University of Dundee

</div>

The [Scottish Theorem Proving Seminar (STP)][STP] will take place on the 7th October, 2015 at the Queen Mother Building, [University of Dundee][Dundee] ([travel information](http://www.computing.dundee.ac.uk/about/travel-information))

For details of previous meetings, see the [STP homepage][STP].

## Invited speakers

### [Helle Hvid Hansen][Helle]

##### [Delft University of Technology][Delft], The Netherlands

**Coinductive specification of k-regular sequences**

*Abstract*

Streams over a set A together with the head and tail operations
are the standard representation of the final A × Id coalgebra. Perhaps less
known is the fact that streams also form a final A × Id^k coalgebra, that
is, a final deterministic automaton on a k-letter alphabet with output in
A. In this talk, I will show how this final deterministic automaton of
streams yields a coalgebraic characterisation of k-regular sequences,
together with coinductive specification formats in the form of behavioural
differential equations using the zip-operations.

(Joint work with Clemens Kupke, Jan Rutten and Joost Winter)

### [Henning Basold][Henning]

##### [Radboud University][Radboud], The Netherlands

**Using Coalgebras to Find the Productive Among the Lazy**

*Abstract*

In this talk, I will discuss how coalgebras can be used to establish
equivalences and predicates for lazy programming languages, and how to
use up-to techniques make the resulting proof methods tractable.

More specifically, we will use a variation of the copattern language
introduced by Abel et al., and show how to characterise a notion of
observational equivalence and productivity for this language.
Moreover, we will introduce some interesting up-to techniques to
simplify proofs of productivity. Finally, if time permits, we use
these techniques to obtain decision procedures for a fragment of the
language.

### [Chris Warburton][Chris]

##### [University of Dundee][Dundee], Scotland

**Scaling Theory Exploration in Haskell**

*Abstract*

We investigate the **theory exploration** (TE)
paradigm for computer-assisted Mathematics and identify limitations and
improvements for current approaches. Unlike the theorem-proving paradigm,
which requires user-provided conjectures, TE performs an open-ended
search for theorems satisfying given criteria. We see promise in TE for
identifying new abstractions and connections in libraries of software
and proofs, but realising this potential requires more scalable
algorithms than presently used.

### [Charles Grellois][Charles]

##### [PPS][PPS] & [LIAFA labs][LIAFA], France

**Coinductive semantics of linear logic and higher-order model-checking**

*Abstract*

A common approach in verification, model-checking consists in computing
whether a given formula holds on an abstract model of interest.
Decidability is usually obtained by standard reasoning on finite graphs
overapproximating the behavior of programs.

The model-checking of functional programs requires however a careful
treatment of higher-order computation, which is a major hurdle to the
traditional abstraction of programs as finite graphs, and leads to the need
for semantic methods.

In this talk, we explain how linear logic provides models of computation
which can be very naturally extended to account for the model-checking
problem of properties of monadic second-order logic, mixing inductive and
coinductive specification, over infinite trees generated by the coinductive
parallel head rewriting of a term with recursion.

This is joint work with my PhD advisor Paul-André Melliès.

### [Fredrik Nordvall Forsberg][Fredrik]

##### [University of Strathclyde][Strathclyde], Scotland

**The encode-decode method in HoTT, relationally**

*Abstract*

In Homotopy Type Theory (HoTT), the `encode-decode' method
makes heavy use of explicit recursion over higher inductive types
to construct, and prove properties of, homotopy equivalences.
The idea is to construct an easier-to-understand family of codes describing
some property of the homotopy equivalence in question, together with
explicit encode and decode functions. The heart of the argument is then to
show that encode and decode form an equivalence between the
easy-to-understand codes and the desired property.

We argue for the classical separation between specification and
implementation, and hence for using relations to track the graphs of
encode/decode functions. Our aim is to isolate the technicalities
of their definitions, arising from higher path constructors, from their
properties.

We describe our technique in the calculation of the fundamental group of
the circle, and comment on its applicability in the current Agda
implementation of HoTT. (Joint work with James McKinna.)

### [Franck Slama][Franck]

##### [University of St Andrews][StAndrews], Scotland

**Automatically proving equivalence by type-safe reflection**

*Abstract*

Dependently typed programming languages encourage us to index our inductive data types (like `A:Type`) over some indices (for instance, a `Nat`), in order to capture some properties (and `A` becomes of type `Nat -> Type`), as it is for example the case with vectors indexed over their length.
But as soon as we start having indices, when defining functions, we run into the classical problem of producing a term of type `(A n)` when it is expected by the type checker to have type `(A n')`. Obviously, if the function is well defined, then the two indices `n` and `n'` should be equal (or somehow equivalent under certain axioms). But being equal doesn't mean that they are syntactically equal, and the type checker can't find the proof of equality on its own : it needs to be produced by hand by the user, usually leading to tons of proof obligations. If we want to encourage the writing of dependently typed data types and programs, we need to have some facilities for producing these proofs of equivalence automatically.

In this talk, I'll present this problem in the dependently typed programming language Idris on a little example, and then show how a specialised reflexive tactic can be easily constructed in Idris for this specific example. The implementation relies on a type safe reflection mechanism, where we represent Idris expressions in a reflected form (indexed over the original expression), from which we can pull out the proof easily. I will then show how this idea can be generalised for the various kind of properties (or axioms) that might be available (for example : associativity, commutativity, distributivity...), leading to a hierarchy of reflexive tactics for Monoids, Commutative Monoids, Groups, Rings and so on, written in Idris, for proving different kind of equivalences. I'll also show briefly show each tactic reuses the other ones from the simplest structures, thus avoiding as much as possible the duplication of code.

This is a joint work with Dr Edwin Brady.

## Schedule

-------------- --------
12:00 - 13:00  *Lunch*
13:00 - 14:00  [Helle Hvid Hansen][Helle]
14:00 - 14:30  [Henning Basold][Henning]
14:30 - 15:00  *Coffee*
15:00 - 15:30  [Chris Warburton][Chris]
15:30 - 16:00  [Charles Grellois][Charles]
16:00 - 16:30  *Coffee*
16:30 - 17:00  [Fredrik Nordvall Forsberg][Fredrik]
17:00 - 17:30  [Franck Slama][Franck]
18:30 -        Dinner at [DCA][DCA]
-------------- -------

## Registration

There are no registration fees, but *we require all attendees to [register by following this link][register].* You can also contact the organisers [via email][contact].

All talk slots are now filled, many thanks to those who volunteered!

[Helle]: http://homepage.tudelft.nl/c9d1n/
[Henning]: http://cs.ru.nl/~hbasold/
[Chris]: http://www.computing.dundee.ac.uk/about/staff/124
[Charles]: http://research.grellois.fr/
[Fredrik]: https://personal.cis.strath.ac.uk/fredrik.nordvall-forsberg/
[Franck]: https://fs39.host.cs.st-andrews.ac.uk

[Dundee]: http://www.dundee.ac.uk/
[Delft]: http://www.tudelft.nl
[PPS]: http://www.pps.univ-paris-diderot.fr
[LIAFA]: http://www.liafa.jussieu.fr
[Strathclyde]: http://www.strath.ac.uk/
[Radboud]: http://www.ru.nl/english/
[StAndrews]: https://www.st-andrews.ac.uk/

[STP]: http://www.macs.hw.ac.uk/stp/
[register]: https://docs.google.com/forms/d/1XcVQGrlJpgJe584TsneKNQ8x2HjBk40n_jhHIazn2nA/viewform?usp=send_form
[contact]: mailto:chriswarbo@gmail.com,komendantskaya@gmail.com
[DCA]: http://www.dca.org.uk/visit/jute-cafe-bar
