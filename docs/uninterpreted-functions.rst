Uninterpreted functions
=======================

A ``declare-fun`` with a nonempty domain declares an uninterpreted function,
and any logic whose name contains ``UF`` enables the support; the
``--uninterpreted-functions`` option (``vc_setFlag(vc, 'u')`` in the C API)
enables it for an input whose logic omits it. Arguments and results may be
``Bool``, bit-vectors, declared sorts, ``RoundingMode`` or floating-point
sorts. Array sorts are refused in a signature.

How a query is decided
----------------------

STP decides congruence -- equal arguments give equal results -- by
refinement over the bit-blasted query, the design Bitwuzla also uses. Each
application ``(f t1 .. tn)`` is *lowered* to a fresh symbol standing for its
result, so the SAT solver sees a query in which every application is a free
value. A satisfying assignment is then a *candidate*: the checker reads the
value of every application's arguments and result, hashes the applications
of each function by their argument tuple, and where two applications with
equal argument values were given different results it has found a
congruence conflict. Each conflict becomes a lemma, ``(and (= t1 u1) ..
(= tn un)) => (= (f t1 .. tn) (f u1 .. un))``, encoded straight to clauses
over the SAT variables the lowering registered, and the solver is asked
again with the lemmas in place. A candidate no conflict refutes is a model;
a solver that runs out of assignments has refuted the query.

Two things happen before the lowering, while an application is still an
ordinary term:

*   The query's own top-level equalities and asserted atoms are pushed
    through the applications (``--uf-propagate-equalities``, on by default).
    A symbol equated with a constant, another symbol, an application or any
    other term free of wide arithmetic becomes that; an application pinned
    to a constant becomes the constant everywhere else; any asserted atom is
    true wherever else it occurs. A query asserting ``x = y`` therefore
    lowers ``(f x)`` and ``(f y)`` as one application, which is the
    structural merge an e-graph solver gets at internalisation, a fact such
    as ``(f 3) = 0`` reaches the arithmetic built on ``(f 3)``, and a bound
    stated on ``x`` under ``x = a + b`` meets the sum. A symbol equated with
    a term holding a multiplication or division at or above
    ``--bv-abstraction-width`` keeps naming it: pushed into every argument
    position, such a term would make each congruence premise a comparison
    of dividers. The defining conjunct is kept, so no model is lost or
    invented. Once lowered, the scalars of an application are protected from
    the simplifier -- a lemma is later encoded over exactly their SAT bits --
    so this is the one point at which such a fact can cross an application.

*   The Boolean skeleton is asked what it forces at the start of every
    round (``--uf-skeleton-preproc``, on by default), and those facts are
    read as well. A verification query states most of its equalities under
    an implication whose guard the structure resolves; this is what lets
    them reach the applications. Asking again after each round matters: a
    round's rewrite renames the atoms and folds connectives, so a guard the
    structure could not see through before it is one it resolves after it.
    On the Certora queries this is the difference between a solve that ends
    in the rewrite and one that bit-blasts millions of gates.

Congruence up front
-------------------

Some declarations are worth constraining before the first solve rather than
lemma by lemma. ``--uf-ackermann`` selects them: ``auto`` (the default)
installs the pairwise congruence constraints of the declarations whose
estimated pair count fits ``--uf-ackermann-budget`` (256 constraints),
cheapest first, ``on`` installs every declaration's and ``off`` none. The
checker runs in every mode, so a declaration the policy left to refinement
is still decided. A declaration whose results are only ever compared with
each other has them narrowed to ``ceil(log2(N+1))`` bits first
(``--uf-narrow-results``), which is what keeps a 256-bit codomain from
costing 256 bits per constraint.

Wide arithmetic
---------------

A solve with uninterpreted functions abstracts its wide multiplications,
divisions and remainders as ``--bv-term-abstraction`` does, without being
asked: ``--uf-bv-term-abstraction`` is ``auto`` by default, which turns the
abstraction on for a solve whose query holds such an operation at or above
``--bv-abstraction-width``, and leaves every other solve as the general flag
says. ``on`` and ``off`` decide it for every UF solve. The general flag is off
by default because on plain bit-vector workloads the abstraction was
measured as a wash; on the UF corpus -- 256-bit contract verification
queries with a handful of products and quotients each, most of which the
search never needs exactly -- it is the difference between finishing and
not. A solve the policy abstracts also admits the quotient-threshold
division schemas for the solve (``--uf-quotient-threshold-schemas``), the
facts these queries contradict; naming the schema groups on the command
line overrides this.

The persistent incremental driver keeps its encoding across solves and is
left on the general flag.

Refinement
----------

``--uf-lemmas-per-round`` caps how many congruence lemmas one refuted
candidate may install before the solver is asked again; the default, 0, is
every conflict the candidate exposes. Every round is a SAT call, so on a
large query the cap only adds rounds.

A candidate the bit-vector abstraction refutes is asked about congruence
too (``--uf-check-during-bv-refinement``, on by default). Equal arguments
implying equal results is a theorem whatever values it is instantiated on,
so the lemma is sound on such a candidate, and installed beside the
abstraction's clauses it keeps the next candidate honest on both counts at
once -- which is what a solver that consults every theory each round does.
Left until the abstraction was faithful, the congruence facts arrived only
after the abstraction had spent its rounds on candidates they would have
refuted outright: on one Certora query thirty-seven solver calls became
three. ``-s`` reports what each stage did: the pre-lowering substitutions,
the eager selection per declaration, the abstraction decision, every lemma
the refinement installs, and a congruence conflict found on a candidate the
abstraction refined.

Models
------

``get-value`` and ``get-model`` read applications through the certified
candidate. An application the rewrite turned into another application --
``(f x)`` under ``x = 7`` is solved as ``(f 7)`` -- is read through its image,
so the value asked for is the one the solve certified. ``define-fun`` output
for a declaration is a nested if-then-else over the argument tuples the
solve observed, with the commonest observed value as the default.
