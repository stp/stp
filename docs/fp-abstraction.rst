Floating-point abstraction
==========================

Word-blasting a binary64 square root builds a 600 k-gate circuit; a
remainder, 2.7 million. STP can instead replace such an operation with a
*surrogate* -- fresh free bits of the operation's own sort -- constrained by
facts that are true of every result the operation can produce: which class
it falls in and with which sign, how it is ordered against its operands,
which binades its exponent can lie in, and what it is when an operand is an
identity. The query solved is smaller than the exact one, and each candidate
the solver comes back with is checked against the exact operation. A
candidate that agrees stands; one that disagrees is refined away by a lemma
that rules out more than that one candidate, and only after a bounded number
of those is the exact circuit released into the running solver.

This is counterexample-guided abstraction refinement over the floating-point
theory, sitting above the SymFPU encoding rather than inside it. It is off
by default and is asked for by name.

Usage
-----

.. code-block:: bash

    stp --fp-abstraction=true query.smt2

``--fp-abstraction``
  Abstract the selected operations. Off by default. Batch solves; the
  incremental driver hosts the abstraction too when
  ``--fp-abstraction-incremental`` is also set, and otherwise encodes
  every floating-point operation exactly.

``--fp-abstraction-ops``
  A comma-separated list of the operations to abstract: ``mul``, ``div``,
  ``sqrt``, ``add``, ``sub``, ``fma``, ``rem``, ``rti``, ``to_sbv``,
  ``to_ubv``. ``default`` is ``mul,div,sqrt,fma``; ``all`` is every one
  of them. An unknown name is refused up front rather than ignored.

``--fp-abstraction-chain-ops``
  The operations abstracted only as links in a chain: an application of one
  of these is abstracted when one of its operands is the result of an
  application already abstracted, and encoded exactly otherwise. The names
  of ``--fp-abstraction-ops``; none by default (see the fma below for what
  the policy was measured to do). An operation named in both lists is
  abstracted wherever it stands.

``--fp-abstraction-width``
  The floor on the packed width, exponent plus significand bits, below which
  an operation is encoded exactly whatever else is set. 16 by default, so
  binary16 is the narrowest format touched; the rules cost about as much as
  a binary16 multiplier and there is nothing to save below it.

``--fp-abstraction-tiers``
  The highest rule tier emitted with a surrogate, 3 by default: 0 is the
  exact class-and-sign shell alone, 1 adds the order facts, 2 the exponent
  bands and overflow selection, 3 the identities. Lower tiers are cheaper
  and prune less; every tier is sound.

``--fp-abstraction-values``
  How many value lemmas one abstracted operation may take before its exact
  encoding is released, 4 by default.

``--fp-abstraction-shape``
  Spend model-instantiated exactness lemmas before value lemmas (on by
  default).

``--fp-abstraction-relational``
  Emit pairwise monotonicity lemmas between abstracted operations that share
  an operand, for a pair the candidate violates (on by default).

``--fp-abstraction-relational-last-width``
  The packed width at or above which a monotonicity lemma is stated only
  once the record's value budget is spent, instead of before its first
  value lemma; 128 by default, 0 never. See the refinement step below for
  what each order costs at each width.

``--fp-abstraction-phase-hints``
  After a refuted candidate, suggest to the SAT solver's decision heuristic
  the operand values it tried and the exact result for them (off by
  default). Measured against: it takes one deep binary128 query from 52 s
  to 32 s and costs the binary64 witness hunts around it (250 to 246 of 256
  solved, 25 queries more than 2x slower), so it stays an option.

``--fp-abstraction-box-lemmas``
  Beside a value lemma for mul/div/sqrt/add/sub/fma/round-to-integral, state
  the widest qualifying box among the tried fraction prefixes, as one
  bit-vector fact (off by default). The box fixes each operand's sign,
  exponent and fraction prefix and keeps the rounding mode fixed. All
  corners must evaluate to finite nonzero results of one sign. Division
  excludes a zero divisor endpoint, and square root requires nonnegative
  inputs. Coordinate monotonicity then bounds every interior result by
  corner results, whose common packed prefix gives the conclusion.
  Remainder is excluded: changes in its nearest integer quotient invalidate
  the corner argument. Integer conversions and other kinds are excluded
  as well. If no box qualifies, the ordinary value lemma still applies.
  Historical measurements
  against: 62% of value lemmas can be widened, and the next candidate is
  rarely in the box, so the extra facts cost more search than they save
  (653 against 658 of 692 engaged queries, a tenth more PAR2).

``--fp-abstraction-repair``
  Before refining a candidate the abstraction refuted, replay the original
  formula under it and accept the candidate as a model when the formula
  holds for its values of the original symbols (on by default).

``--fp-abstraction-constant-operands``
  Whether an operation one of whose float operands is a constant is
  abstracted: ``auto`` (the default), ``on`` or ``off``. A constant's
  circuit is small and propagates -- a multiplication by a constant is a
  shift-and-add network the blast prunes to the constant's set bits, and the
  SAT solver drives it from the other operand -- where the abstraction puts
  a free result in its place, under rules the solver then has to search.

  Which is faster depends on what the query does with its constants, and the
  two corpora disagree. On the converted flux-balance QF_FP queries, where
  every multiplication is a coefficient times a variable and the query is
  linear, abstracting them turns two-second solves into timeouts: declining
  them solves four more of 275. On the KLEE corpus a product by a constant
  is a step of a Horner polynomial in library code, where the abstracted
  result feeds the next product and the rules carry it: declining them costs
  fourteen solves of 1,241 hard queries and a tenth of the PAR2.

  ``auto`` reads the difference off the query. If the configuration would
  abstract an operation with two float operands the blast does not know, or
  one whose operand is another abstracted operation -- a product of two
  unknowns, or a chain whose result feeds the next link and which the order
  and band rules carry along -- then the query computes with its unknowns
  and the constant operands are abstracted with the rest. If it would do
  neither, every record would be one coefficient times one unknown standing
  alone, the query is linear over its coefficients, and they are left exact,
  the ``-s`` report saying so and counting them. It is read once, from the
  prepared formula, and over the kinds ``--fp-abstraction-ops`` admits: an
  operation that is not going to be abstracted neither chains nor searches. A piece the incremental driver
  hands over is not the session, so ``auto`` abstracts there.

``--fp-abstraction-significand-bits``
  The significand bits of the reduced-precision bands emitted with an
  abstracted multiplication, division or square root (8 by default; 0 emits
  none). See the facts below.

``--fp-abstraction-significand-bits-wide``
  The same at packed widths of 128 bits and above (16 by default; 0 uses the
  narrow setting everywhere). A 16 x 16 band is a fraction of a percent of a
  binary128 multiplier, and on the queries symbolic execution raises over
  binary128 LAPACK it is the difference between a candidate that needs its
  value and one that does not: 427 of 436 engaged queries solved against
  421 with 8-bit bands, nothing lost, the PAR2 down by a quarter; at
  binary64 it is neutral, which is why the width is the switch.

``--fp-abstraction-restart-width``
  The packed width at or above which releasing a multiplication, division,
  square root, fma or remainder runs the whole pipeline again with that
  operation lowered exactly, instead of splicing its circuit into the
  running solver. 0, which never restarts, unless ``--bv-term-abstraction``
  is on, when the command line sets 128: the restart exists so that the
  bit-vector abstraction can see the released circuit, and below 128 bits
  that circuit is not worth the learnt clauses a restart throws away. See
  the release step below.

Which operations are abstracted
-------------------------------

By default: ``fp.mul``, ``fp.div``, ``fp.sqrt`` and ``fp.fma``, at any
format of at least 16 packed bits. The first three are the operations whose
exact circuits are large next to what the rules cost, and whose rule tables
decide most of the unsatisfiable properties they are asked about without
ever releasing the circuit.

``fp.fma``
  One rounding of ``x*y + z``, never modelled as a product followed by a
  sum. Its finite-range pruning is weaker than the multiplier's; what
  carries it are the facts against a product of the same factors or a sum
  with its addend when those are abstracted too (below), and the
  monotonicity lemmas. It is in the default set because it is the operation
  compiled numerical code is full of -- ``a*b + c`` contracts to one -- and
  because abstracting every one measured as a gain on every corpus of such
  code: on the queries symbolic execution raises over SUNDIALS kernels it
  took half off the PAR2 of the other three at binary64 and a seventh at
  binary128 with no loss, on binary64 LAPACK two more of 794 queries and a
  tenth off the PAR2 (with as many losses beyond 2x as wins: the Householder
  reflections of ``geqrf`` lose, the triangular solves win), on binary128
  LAPACK and Cuba a query either way between runs and a twentieth off, with
  48 wins beyond 2x against 3 losses. The alternative that
  was measured first, abstracting an fma only as a link in a chain
  (``--fp-abstraction-chain-ops=fma`` with the fma out of
  ``--fp-abstraction-ops``), takes every SUNDIALS gain -- their fmas run
  over abstracted products -- and none of LAPACK's, whose fmas accumulate
  over inputs and feed a quotient only at the top, which a bottom-up chain
  never sees; it came out below both.

The remaining ones are complete and verified, and are opted into with
``--fp-abstraction-ops``:

``fp.to_sbv``, ``fp.to_ubv``
  The integer conversions, over their totalised form: the surrogate is a
  plain bit-vector at the target width -- the one abstractable result
  that is not a float -- and the totalised unspecified value rides as one
  more proxy, so NaN, the infinities and out-of-range go to it by a rule
  while the exponent bands bound every in-range result without the
  rounder. The literal evaluator answers what the operand's class and
  exponent decide and leaves symfpu the trap-free window; the narrow
  rounding boundary costs a release. Their weight is incremental: on an
  industrial corpus of 18,367 incremental sessions, 19% convert (3,513),
  and on a 150-session sample the hosted abstraction with conversions is
  answer-identical to the exact driver at level time, engaging 136
  sessions. In batch,
  SMT-LIB holds 313 such files (KLEE's float-to-string shapes); replaying
  all of them, the abstraction agrees everywhere and wins nothing -- the
  conversions' measured value is the hosted sessions.

``fp.rem``
  Exact (no rounding mode), with the largest circuit of any operation and a
  small table; every release avoided is a large saving, and the table is
  cheap to carry.

``fp.add``, ``fp.sub``
  Subtraction is addition of the negated second operand, and the two share
  one table. An isolated sum is cheap to encode exactly and abstracting it
  buys little; in a chain of abstracted operations, or beside a product it
  shares an operand with, it lets the whole chain be refined at the level
  of the rules -- which is what ``--fp-abstraction-chain-ops=add,sub`` is
  for, though it is not yet measured.

``fp.roundToIntegral``
  Opt-in as ``rti``. Its circuit is small (under 4 k gates at binary64)
  and on its own not worth a refinement loop; what changes that is a query
  relating several roundings, where the exact encoding's difficulty grows
  with the relation and the abstraction's does not (below).

Not abstracted, and not worth it: conversions to a float (``to_fp``),
``fp.min``/``fp.max``, ``fp.abs``, ``fp.neg`` and the predicates, which are
cheap already. Under ``--incremental`` nothing is abstracted unless
``--fp-abstraction-incremental`` is set.

An operation is abstracted once per distinct application: a product that
appears in three places, or as ``(fp.mul rm x y)`` in one and
``(fp.mul rm y x)`` in another, gets one surrogate. A symbolic rounding mode
is admitted; the rules that depend on the mode are then written as a case
split over it.

How the abstraction is built
----------------------------

Every abstracted application ``t = op(rm, x, y)`` becomes a fresh
bit-vector symbol of the packed width, read as a float through
``(_ to_fp eb sb)``. Its operands are *proxies*: a bit-vector symbol ``p``
with the definition ``(= ((_ to_fp eb sb) p) x)``, or the surrogate of an
inner abstracted operation when the operand is one. Everything the
abstraction later says is said over those symbols, so a lemma about an
operation is a circuit over bits the SAT solver already has, and the proxies
and surrogates are protected from the preprocessing that would otherwise
substitute them away.

The rules are emitted at abstraction time, all of the admitted tiers, over
the packed fields of those symbols: sign, exponent and fraction are slices,
the classes are tests on the fields, ordering and equality are STP's own
native float comparisons over packed bits, and the exponent arithmetic is a
few bits wider than the exponent field. At binary64 the whole table for a
multiplication costs about 3 k gates against 39 k for the multiplier; for a
square root, under 1 k against 612 k.

How a wrong candidate is refined
--------------------------------

The candidate is read at the end of the bit-vector refinement and before the
final model check, one abstracted application at a time in construction
order, so an inner operation of a chain is checked before the outer one that
consumes it. Each application's exact result is computed from the
candidate's operand values with the literal evaluator and compared under
SMT-LIB equality (every NaN is one value, the two zeros are two). An
application whose candidate disagrees is first replayed: the original
formula mentions no surrogate and evaluates every operation exactly, so if
it holds for the candidate's values of the original symbols the candidate
is a model, whatever its surrogates said, and nothing is refined
(``--fp-abstraction-repair``; ``-s`` counts these as model repairs). A
property that constrains a result only through what the rules already
guarantee -- its class, its sign, a bound the bands imply -- is decided
this way on the first candidate. Otherwise it is refined by the first of
these that applies:

1. an *exactness lemma*, instantiated from the model: a product of two
   values that are multiples of ``2^a`` and ``2^b`` is a multiple of
   ``2^(a+b)`` while no overflow is possible (a sum or remainder, of the
   smaller quantum; a fused multiply-add, of the smaller of the product's
   and the addend's), which cuts every candidate of the wrong shape, not
   just this one; at most two per application;
2. a *relational lemma* against another abstracted application of the same
   operation, mode and format, when the candidate violates it: congruence,
   when the two applications' operands are equal in the candidate (under
   SMT-LIB equality, the product's factors in either order -- the records
   themselves are only merged on syntactic sharing) but their results are
   not; or monotonicity, when they share every operand but one and a larger
   free operand did not give a larger (or, in the direction of the shared
   operand's sign, a smaller) result. Each is a universal fact and is
   asserted once. At and above ``--fp-abstraction-relational-last-width``
   this step moves below the value lemmas: stated first, these facts carry the binary32
   witness hunts whose records share operands (``griggio``'s ``sin`` and
   ``sqrt`` loops take 7 to 70 of them and build no circuit), stated last
   they keep a wide witness hunt from stalling under them (at binary128 each
   is a pair of wide comparators, and eight in one round left six LAPACK
   triangular solves at a 30 s timeout that take 3-9 s with the facts held
   back). Neither order wins on both corpora, so the width decides: the
   first order below 128 bits, the second from 128 bits on, which on the
   692 engaged KLEE queries is four more solved with nothing lost;
3. a *value lemma*: the complete argument tuple, including a symbolic mode
   and a conversion's totalisation choice, gives exactly this result
   (``isNaN`` for a semantic FP NaN, but exact NaN bits in a bit-precise
   host); at most ``--fp-abstraction-values``
   per application;
4. the *release*: ``(= t (op rm x y))`` over the proxies, encoded once
   through the same bit-blaster the query used and spliced onto the live
   solver's variables. After it, the application is exact and is not
   checked again.

   A splice gets none of what the ordinary lowering gives a circuit:
   constant-bit propagation, the simplifier, and -- when
   ``--bv-term-abstraction`` is on -- the bit-vector abstraction of the wide
   significand multiplier or divider inside it, which at binary64 is the
   difference between a 39 k-gate multiplier and a 7 k-gate one, or a 612 k-
   gate square root and a 13 k-gate one. So with the bit-vector abstraction
   on, at or above ``--fp-abstraction-restart-width`` a released
   multiplication, division, square root, fma or remainder is instead
   lowered by running the pipeline again over the same formula with that
   operation held out of the abstraction; everything else stays abstracted
   and the learnt clauses of the run are lost. Those clauses outweigh the
   smaller circuit at binary64: on 2,535 binary64 queries from symbolic
   execution of LAPACK, GSL, openlibm and other libraries, releases spliced
   in place solved 2,454 against 2,429 by restart, with the PAR2 score down
   19% -- the same on two builds a week apart, with no other width moved --
   so the command line restarts from 128 bits. Without the bit-vector
   abstraction the restart is off: what constant-bit propagation and the
   simplifier win back on the released circuit is less than the lost
   clauses cost, and at 128 bits every restart pays a multi-second exact
   solve again -- on 753 binary128 queries from symbolic execution of
   LAPACK and Cuba, releases spliced in place solved 745 against 743 by
   restart and lost no query to the exact encoding where the restart lost
   two. On 311 independent binary128 queries
   from that symbolic execution, the two abstractions together
   (``--fp-abstraction=true --bv-term-abstraction=true``, the restart on)
   are the best configuration measured, 302 solved against 291 for the
   floating-point abstraction alone with half the PAR2 and no query lost;
   the bit-vector abstraction supplies the significand multiplier and
   divider a released circuit would otherwise blast whole. The application is remembered by
   its node in the prepared formula, and a pass that mints fresh symbols
   (the totaliser does, for the unspecified results of partial conversions)
   can rebuild it under another node in the next run, which then abstracts
   it again: so a run that abstracted no fewer applications than the run
   before it splices its releases instead, and
   ``--fp-abstraction-restart-limit`` (4) bounds the runs regardless.
   ``-s`` reports each restart and the final run's statistics count them.

Primary shape, relational and value lemmas are checked for violation by
the current candidate before being queued. Optional box constraints
accompany a cutting value lemma; they are not a separate progress step.
If the literal evaluator cannot supply an exact
result, the record goes directly to exact release; that equality need not
exclude the candidate, but it makes one more record exact.

Queued releases and committed releases are distinct states. Only after
the exact equality has been asserted and recorded in the permanent ledger
may a record be skipped by later candidate checks. Accepting model repair
discards queued releases and phase hints, and restores per-record budgets
and relational bookkeeping. This is essential when an incremental query
reuses those records. A SAT-backend rebuild reasserts committed facts.

An answer of ``sat`` is reported either from consistent exact records or
from an exact replay accepting the interpretation of original symbols.
Return that interpretation; nested auxiliary values, if needed, are
reconstructed child-first. An answer of ``unsat`` relies on every asserted
rule and lemma being implied by the exact operation. With finite per-query
budgets and eventual committed release, termination does not require every
release to cut the current candidate. It assumes a terminating exact
backend for the supported input fragment, without resource exhaustion.

Which facts are offered
-----------------------

Each operation's table is a set of guarded implications over packed fields.
Dedicated C++ tests assert ``exact ∧ ¬rule`` unsatisfiable for the emitted
rules at explicit format, rounding-mode and parameter combinations. Such a
check establishes those instances and nothing more: none of them proves a
rule for every format.
The tiers, with the multiplication table as the example:

.. list-table::
   :header-rows: 1
   :widths: 8 24 68

   * - Tier
     - Family
     - What it says
   * - 0
     - shell, sign
     - When the result is NaN, exactly; partial constraints on infinity and zero; its
       sign from the operands' signs; that two subnormals cannot make a
       normal above the smallest.
   * - 1
     - order
     - ``|y| >= 1`` gives ``|x*y| >= |x|``, and ``|y| <= 1`` the reverse;
       for a square root, the bracket between 1 and its argument; for a
       sum, that adding a non-negative moves up.
   * - 2
     - bands, overflow
     - Two normals whose exponents sum inside the range give a normal within
       one binade of that sum, and within it the fractions order (in the
       lower binade the product's fraction is at least each factor's, in
       the upper at most; a quotient's the other way against the
       dividend's); at the top of the range, the overflowed result in each
       rounding mode (infinity, or the largest finite, by mode and sign);
       at the bottom, a zero or subnormal.
   * - 3
     - identities
     - ``x*1 = x``, ``x*-1 = -x``, scaling by a normal power of two is
       exact; ``x/x = 1``; ``sqrt 1 = 1``; absorption of an addend far
       below a normal, exactly under round-to-nearest and to a neighbour
       in the rounding direction otherwise.

The exponent bands say which binade a result is in; the *significand
bands* say where in it. The top ``k`` bits of each operand's significand
(``--fp-abstraction-significand-bits``) bracket the operand to one part in
``2^(k-1)``, the exact product of the brackets' ends is a ``k×k`` integer
product, rounding is monotone and -- with ``2k+1 ≤ p`` -- both ends are
representable, so the rounded result lies between them; each end is
compared with the result's significand at the shift its binade dictates.
A quotient is bracketed without a divider (the result times the divisor's
bracket against the dividend's, with a ``k``-ulp of slack for the one
rounding) and a root without a root (the squares of the result's bracket
against the argument). At binary64 with ``k = 8`` the three add 1.3 k,
1.7 k and 2.1 k gates to a record's rules and cut what a wrong candidate
can be from a factor of two to about one percent, which is what a value
hunt needs: the exponent bands alone leave the value lemmas to rule out
candidates one at a time.

Between operations, a fused multiply-add is related to the other records
over its operands under the same mode, as matching records become available:
against the product of its factors, a
non-negative addend keeps it at or above the product and a non-positive one
at or below, and a zero addend to a nonzero product makes the two one value
(one rounding of the same exact value); against the sum of a factor with the
addend, a unit other factor makes the two one value. These need no candidate
and are emitted with the rules; ``-s`` counts them as cross-operation rules.
Incremental construction tracks each FMA/partner/role relationship separately
and attaches it to both records. A later piece using either participant
therefore carries the relationship and both records' transitive definitions;
an earlier piece need not remain active. Repeated discovery does not emit
the relationship again.

The rule schemas' mathematical format domain, abstraction admission and
exact-backend support are distinct. Abstraction admits source formats with
``2 <= eb <= 56`` and ``2 <= p <= 4096``, subject to operation selection and
the width floor. An operation outside this policy stays exact only when
the backend supports it. In particular, exact remainder requires
``2^eb + p - 4 <= 2304``; binary128 remainder is rejected. The correctness
and termination argument assumes a well-sorted quantifier-free query and
a sound, terminating exact host for its operations.

Format guards are part of the validity and selection conditions, including
the divider/square-root exponent-range restrictions, integral-rounding
closure, significand-band precision and conversion target widths. Initial
conversion rules are omitted for ``m < 2``: the signed bound ``[-1,1]``
would otherwise exclude the defined result zero. Totalisation choices are
function values keyed by operation, format, target width, mode and semantic
FP input, with NaNs canonicalised. They are neither a shared global
constant nor independent choices per occurrence. Exponent comparisons in
conversion rules are widened to represent the target width as well as
the source exponent; wide negative multiplicity thresholds are signed,
not zero-extended uint64 values.

What the monotonicity lemmas decide
-----------------------------------

A property that relates two applications of one operation is where the
exact encoding is weakest and the relational lemmas strongest. That
``x >= 0`` and ``y1 <= y2`` give ``x*y1 <= x*y2`` is two binary32
multipliers and a theorem about them when bit-blasted, which the SAT solver
does not finish in minutes; abstracted, the first candidate violates the
monotonicity fact between the two records, the fact is asserted, and the
query is unsat in under a tenth of a second with neither multiplier ever
built (``tests/query-files/fp-abstraction-tests/relational-mul-unsat.smt2``;
``relational-div-unsat.smt2`` is the same for two binary64 dividers). With
``--fp-abstraction-relational=false`` the same queries refine by value
lemmas and release, and are back to the exact encoding's difficulty.

The same shape is what makes ``fp.roundToIntegral`` worth abstracting at
all. Two roundings at the ends of a chain of ``fp.leq`` bounds, and the
claim that the last is below the first, is 14 s for the exact encoding at
binary64 with sixteen bounds and 35 s with thirty-two; at binary128, 59 s
and 274 s; a single pair at binary256, 35 s. With ``--fp-abstraction-ops=rti``
each is one monotonicity lemma and one round: 1.2 s, 2.4 s, 2.2 s, 5.5 s and
0.6 s (``rti-chain-monotone-unsat.smt2`` is the sixteen-bound case). On a
query that needs the value of one rounding -- ``x`` in an interval and its
rounding not the integer in it -- the rules bound the result to a binade,
the value lemmas rule out one candidate at a time, and the release follows:
the loop costs a little where the circuit costs nothing, which is why the
operation is not abstracted by default.

Reading what happened
---------------------

``-s`` (or ``-t``) reports one line per solve:

.. code-block:: text

    FpAbstraction: 3 abstracted (1 shared occurrences, 4 candidates, 0 by chain), 63 rule conjuncts, 0 cross-operation rules, 9 checks, 4 inconsistent, 1 shape lemmas, 2 value lemmas, 0 relational lemmas, 1 releases, 4 rounds, 0 restarts, 0 model repairs, 0 box lemmas, 0.02 s encoding lemmas

*candidates* are applications of an admitted operation seen at or above the
width floor; *abstracted* are the records made for them, *shared* the
occurrences that reused one, *by chain* the records admitted through
``--fp-abstraction-chain-ops``; *cross-operation rules* are the facts between
an fma and its partner records. *checks* are record checks against a
candidate; *inconsistent* those that disagreed with the exact value, each
followed by one of the four refinements counted after it. *rounds* is how
many refinement rounds encoded a floating-point lemma; *box lemmas* and the
seconds spent *encoding lemmas* are the two experiments' counters. A solve
that ends with no releases decided the query on the rules alone. A second line
breaks the records down by operation:

.. code-block:: text

    FpAbstraction by operation: mul 2 records (1 released, 0 shape lemmas, 3 value lemmas) div 1 records (0 released, 0 shape lemmas, 0 value lemmas)

so a corpus can be read for what it asks of each operation -- how many of
its records reached their exact circuit, and how many lemmas they took on
the way -- which is what decides whether an operation belongs in
``--fp-abstraction-ops``.

Checking the answer
-------------------

``-d`` (``--check-sanity``) runs the ordinary model check, which evaluates
the original query, exact operations included, under the model reported, so
solving a query with and without the abstraction under ``-d`` and comparing
the answers is a differential test of it;
``tests/query-files/fp-abstraction-tests/`` runs the refinement loop end to
end in the test suite.
