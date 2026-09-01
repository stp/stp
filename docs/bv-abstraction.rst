Bit-vector abstraction
======================

Bit-blasting a 256-bit division builds a divider. STP can instead replace
such an operation with fresh free bits, solve the smaller query that leaves,
and check the candidate the solver comes back with: if it satisfies the
operation the answer stands, and if it does not, refinement adds clauses that
rule the candidate out and the search runs again. What it adds is either a
fact true of *every* pair of operands, or -- as the backstop -- the exact
circuit the query would have had all along.

This is counterexample-guided abstraction refinement over the bit-vector
theory, and it is off by default. It is asked for by name.

The division and remainder facts, and most of the multiplication and addition
ones, are not STP's. They come from

  Aina Niemetz, Mathias Preiner, Yoni Zohar. *Scalable Bit-Blasting with
  Abstractions.* CAV 2024, LNCS 14681, pp. 178-200.
  `doi:10.1007/978-3-031-65627-9_9 <https://doi.org/10.1007/978-3-031-65627-9_9>`__

and are reimplemented against STP's own bit-blaster.

Usage
-----

Two independent switches turn abstraction on, and nothing happens without at
least one of them:

``--bv-term-abstraction``
  Abstract wide ``bvmul``, ``bvudiv`` and ``bvurem``; ``bvadd``, ``ite``
  over bit-vectors and the bit-vector comparisons can be added, see below.

``--bv-eq-abstraction``
  Abstract wide equalities, refining them through congruence closure at word
  level.

``--bv-abstraction-width`` is the floor for both: an operation narrower than
this (64 bits by default) is encoded exactly, whatever else is set. Nothing
below that width is ever abstracted, so a query of 32-bit arithmetic is
untouched by any of the options here.

.. code-block:: bash

    stp --bv-term-abstraction=1 wide-division.smt2

Which operations are abstracted
-------------------------------

Once ``--bv-term-abstraction`` is on, each family can be excluded:

.. list-table::
   :header-rows: 1
   :widths: 42 12 46

   * - Option
     - Default
     - Operations
   * - ``--bv-term-abstraction-mult``
     - on
     - ``bvmul``, and ``bvudiv``/``bvurem`` unless the next option is also
       given
   * - ``--bv-term-abstraction-divmod``
     - on
     - ``bvudiv`` and ``bvurem``, overriding the option above in either
       argument order
   * - ``--bv-term-abstraction-plus``
     - off
     - ``bvadd``
   * - ``--bv-term-abstraction-ite``
     - off
     - ``ite`` over bit-vector terms
   * - ``--bv-term-abstraction-compare``
     - off
     - the bit-vector comparison predicates

Multiplication and division are separable because their circuits cost very
differently and the workloads that benefit from abstracting them are not the
same. The comparison, ``ite`` and addition families are cheap either way:
each defines itself in a single refinement round rather than by enumerating
operand values, so abstracting them saves little. On bit-vector workloads
turning them on or off is noise -- 204 against 203 solved over 329 QF_BV
files the abstraction engages on, and 247 against 245 over 400 256-bit
industrial queries -- but inside a floating-point circuit they are hundreds
of 106- to 229-bit if-then-elses and adders around a handful of
multiplications and dividers, and abstracting them cost one KLEE binary128
query 34 s where the arithmetic alone takes 3.4 s. They are off by default
for that reason.

How a wrong candidate is refined
--------------------------------

Comparisons, ``ite`` and addition are pinned exactly the first time a
candidate contradicts them, and are then done with.

Multiplication, division and remainder have no compact exact lemma, so their
refinement has three tiers:

1. **An algebraic fact.** Something true of every pair of operands that this
   candidate contradicts -- ``b != 0 -> q <=u a`` for a quotient, the
   product's trailing zeros for a multiplication, and several dozen more.
   One such fact excludes a region of the candidate space.

2. **A blocking lemma.** When no fact is contradicted, the one pair of
   operand values the candidate holds is settled: ``a = va /\ b = vb ->
   t = va op vb``. This excludes one pair out of 2^(2W), which is why there
   is a bound on how many are spent. It is written through one fresh
   variable standing for the premise -- a clause of 2W+1 literals and then
   W binary clauses -- rather than repeating the premise in every result
   clause, which at the widths of binary128 significand arithmetic made
   each lemma a hundred thousand literals that every later SAT call paid
   for.

3. **The exact circuit.** Once the blocking allowance is gone, refinement
   stops enumerating and says what the operation is, using the same
   bit-blaster entry point an unabstracted query would have used -- with the
   operand bits the original blast already knew, so a multiply against a
   literal does not become a fully symbolic multiplier.

``--bv-term-abstraction-schemas`` (on by default) governs the first tier. Off,
each operation falls back on its own tier-2 or tier-3 behaviour, which is what
the abstraction did before the facts existed and is the comparison they have
to earn their keep against.

The blocking allowance
----------------------

``--bv-term-abstraction-rounds`` (32) caps tier 2. Through about thirty rounds
the abstraction is still two to four times faster than not abstracting; by
sixty it is break-even; past that it collapses -- a 64-bit factorisation spent
5816 rounds and ninety seconds on a query the unabstracted solve answers in
five hundredths of one. Zero never escalates and enumerates without limit.

Two optional refinements of that allowance:

``--bv-term-abstraction-value-divisor``
  Make the allowance ``width / this`` instead, floored at one and capped by
  the ceiling above. The argument for it is that a blocking lemma rules out
  one pair out of 2^(2W), so thirty-two of them is a third of an eight-bit
  operand's pairs and one part in 2^101 of a fifty-three-bit one's. Off by
  default: it measured as a wash at two abstraction widths.

``--bv-term-abstraction-divmod-value-limit``
  Cap ``bvudiv``/``bvurem`` blocking independently, after the ceiling and any
  width scaling. Unlike changing the ceiling this leaves the algebraic-schema
  budget and multiplication untouched, which is what makes a 4/8/16/32
  divider experiment a comparison of one thing. Zero (the default) adds no
  cap. It is a measurement control, not a recommended policy: on a broad
  417-query population 4 and 8 were clear regressions and 16 was slower.

The allowance is spent per query. A record's life is one query in the batch
pipeline but a whole session under the incremental driver, so counting from
its lifetime would make the same flag mean "per session" there.

``--bv-term-abstraction-inc-bitblast`` escalates a multiplication a piece at a
time -- only the bits up to and a little past the lowest one the candidate got
wrong. The low bits of a truncated product depend only on the low bits of its
operands, which is what makes the partial encoding a theorem rather than a
guess, and is why it is multiplication alone: a quotient's low bits depend on
the whole of both operands. Off by default, since each piece repeats the work
for every lower bit.

Which facts are offered
-----------------------

The catalogue is partitioned into families, and
``--bv-term-abstraction-schema-groups`` takes a comma-separated list of them.
``all`` and ``none`` stand alone; ``udiv``, ``mul6``, ``quotient-one`` and
``divrem-identity`` are aliases for common combinations.

.. list-table::
   :header-rows: 1
   :widths: 26 74

   * - Family
     - What it holds
   * - ``base``
     - The schemas an enabled abstraction inherits: the qualified division
       facts, the divisor-value and bound schemas, and multiplication's
       parity, trailing-zero and power-of-two schemas.
   * - ``udiv15``
     - ``x >=u ((t << 1) >> (t << s))``, the highest-firing single division
       fact outside ``base``.
   * - ``udiv-observed``, ``udiv-tail``
     - The rest of the division registry: the facts that fired on the
       qualification corpus, and the ones that did not.
   * - ``urem``
     - The remainder registry.
   * - ``quotient-one-quot``, ``quotient-one-rem``
     - The band where the divisor fits its dividend exactly once:
       ``s <=u x <u 2s`` forces ``q = 1`` and ``r = x - s``.
   * - ``quotient-thresholds``
     - ``q >= 2^k <-> b <=u (a >> k)``, which excludes a whole
       quotient-magnitude band with one comparison.
   * - ``divisor-magnitude``
     - ``b >=u 2^k -> q <=u (a >> k)``, with ``k`` read off the candidate.
   * - ``divrem-full``
     - ``x = q*s + r`` over a quotient and remainder that share operands.
       It builds a full-width multiplier.
   * - ``mul8``, ``mul-ref3``, ``mul-tail``
     - The multiplication registry, in three ranked bands.
   * - ``add``
     - The addition registry.
   * - ``low-prefix``
     - The exact low bits of a product or a sum.

Profiles
--------

``--bv-term-abstraction-profile`` selects a family mask and a round ceiling
together, as one decision. The two lower-level options cannot be combined
with it.

``qualified``
  ``base``, ``urem`` and ``mul-ref3`` at 32 rounds. This is the default, and
  the only mask the corpus qualification justified: ``urem`` turns the wide
  remainder cases from a two-gigabyte external timeout into fractions of a
  second, and ``mul-ref3`` takes one 512-bit rewrite candidate from
  3.66s/766MB to 0.12s/65MB.

``broad``
  The complete observed single-record catalogue -- every fact that states
  something about one operation on its own -- at 16 rounds.

``aggressive``
  ``broad`` plus ``divrem-full``. It reduces blocking and exact escalation
  the most of any profile and is still the slowest of them, because the
  paired identity builds a full-width multiplier. It exists to make that
  trade reproducible.

Families outside every profile are selectable but not recommended. ``add``
and ``low-prefix`` were measured and deliberately not adopted: over 497
queries chosen because they abstract a wide addition -- the family's best
case -- enabling ``add`` installed 30,519 lemmas, cost 19.9% and seven
solves, and regressed 162 queries while improving 15; ``low-prefix`` fired
9,525 times and moved nothing. They stay selectable so those results stay
reproducible.

Which CNF generator
-------------------

The abstraction's search is many-solve: every refinement round is another
call on a solver that keeps the whole CNF, and which CNF it keeps decides
how that search goes far more than it decides one solve. With
``--cnf-generation-effort`` at ``auto``, turning
``--bv-term-abstraction`` on therefore selects the Gia backend at its lowest
rung (``gia-low``) rather than the size-based choice between ``very-low``
and ``medium``, and ``-s`` says so:

.. code-block:: text

    cnf-auto: BV term abstraction on, chose gia-low

Over 311 KLEE binary128 queries with multiplication and division abstracted,
the size-based rung solved 300 with PAR2 2024 and ``gia-low`` 306 with PAR2
1356 (Bitwuzla: 308 and 1647); without the abstraction the same rung is
worth far less there, 286 against 283 solved, which is why the size-based
choice stays for everything else. On 329 SMT-LIB QF_BV files where the
abstraction engages it costs nothing, 216 solved against 204 either way.
An explicit level is always left alone.

Reading what happened
---------------------

``-t`` reports what reached the bit-blaster, what the abstraction took, and
what refinement spent:

.. code-block:: text

    Abstraction coverage (candidates -> abstracted): eq=2->0 compare=2->0 ite=1->0 plus=1->0 mult=1->1 divmod=0->0
    Abstraction refinement: rounds=6 blocking=1 schema=4 exact=1 exact-mult=1 exact-divmod=0
    Abstraction circuit cost: clauses=33968 variables=8160 microseconds=4210
    Abstraction schema cost: clauses=512 variables=64 microseconds=95
    Abstraction schemas by group: base=3 udiv15=0 ... urem=1 ...
    BV abstraction record: record=0 node=41 kind=BVMULT width=64 state=exact blocking=1 schemas=0 exact=1 exact-bits=64 allowance=32 paired=0 pair-full=0 ...

Coverage counts operations reaching the bit-blaster at or above the width
floor, not occurrences in the query text: reading them off the text
over-counts, because it counts arithmetic the simplifier has already retired.
Escalations are split between multiplication and division because equal
counts can hide very different trades -- an exact multiplier is affordable
where an exact divider may not be. The two cost lines are separate because
one lemma is not one price, and rolled in with an exact divider a schema
total would be invisible. The per-record lines expose the blocking
distribution that an aggregate hides.

``--exit-after-CNF -t`` prints the coverage line without solving anything.
Bit-blasting is where those counters are filled, so it is a cheap way to find
which files in a corpus contain arithmetic wide enough to abstract at all.

Everything above is also readable from the C interface: ``vc_getCounter`` for
the totals, ``vc_getSchemaGroupCounter`` and ``vc_schemaGroupName`` for the
per-family breakdown, and ``vc_setSchemaGroups`` and the
``BV_TERM_ABSTRACTION_*`` interface flags to configure a run.

A caveat about partial CNF
--------------------------

An abstracted encoding is an over-approximation of the query, so
``--output-CNF`` and ``--exit-after-CNF`` produce a CNF that is not the
problem. No flag completes it -- turning the abstraction off is a different
encoding, not the same one finished -- and STP says so at both exits. This is
unlike array read refinement, whose partial CNF is completed by
``--ackermanize``.

Evaluation
----------

``scripts/benchmark-bv-refinement.sh`` compares configurations over a
directory or a manifest of queries, blocking runs by (repetition, query) and
rotating the variant order inside each block so machine drift does not
systematically favour one setting. It reads the machine-readable telemetry
above rather than parsing prose.
``scripts/check-benchmark-bv-refinement.sh`` exercises the harness against a
deterministic fake solver. Neither is wired into CTest: they need ``bash``,
``timeout``, ``sha256sum`` and ``/usr/bin/time``, so the coverage would
silently disappear on a platform missing one.
