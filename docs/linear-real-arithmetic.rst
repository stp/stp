Linear real arithmetic
======================

STP decides quantifier-free linear real arithmetic exactly: ``QF_LRA``, and
with uninterpreted functions ``QF_UFLRA``. A Real is a mathematical rational,
not a float and not a bit-vector, so there is nothing to bit-blast. Each
linear predicate becomes one Boolean atom of the SAT search. A simplex over
exact rationals decides whether the atoms the search has made true fit
together, and a conflict it finds goes back to the search as a clause. This
is the DPLL(T) arrangement of Dutertre and de Moura ("A Fast
Linear-Arithmetic Solver for DPLL(T)", CAV 2006), whose general simplex STP
implements.

Two layers sit on top of the exact core and are on by default. A presolve
rewrites the query before any atom is made, and a double-precision simplex
does most of the checking while the search runs. Neither can change an
answer. Every conflict the float tier reports is certified exactly before
the search sees it, and every model, from whichever layer, is checked in
exact arithmetic against the query as written before it is printed.

Usage
-----

.. code-block:: lisp

    (set-logic QF_LRA)
    (set-option :produce-models true)
    (declare-fun x () Real)
    (declare-fun y () Real)
    (assert (or (< (+ x y) 1) (> (+ x y) 10)))
    (assert (>= x 1))
    (assert (>= y 1))
    (assert (<= (- x y) 3))
    (check-sat)
    (get-model)

.. code-block:: text

    sat
    (
      (define-fun |x| () Real 7)
      (define-fun |y| () Real 4)
    )

The terms are ``+``, ``-`` (binary and unary), ``*`` and ``/``, over
numerals and decimals (``3``, ``2.25``). The predicates are ``=``,
``distinct``, ``<``, ``<=``, ``>`` and ``>=``, and ``ite`` over Reals
works. Linear means that a product needs a constant on one side and a
quotient a nonzero constant divisor. ``(* x y)`` and ``(/ x y)`` are
refused with an error when the term is built rather than answered
``unknown``. There is no ``Int`` sort, so ``to_real``, ``to_int`` and
``is_int`` are not available. A value is printed as an exact rational:
``(/ 3 2)``, ``(- (/ 9 4))``.

``Real`` is a sort only under ``QF_LRA`` and ``QF_UFLRA``. The ``*FPLRA``
logics keep their floating-point meaning, in which a real appears only as
the literal argument of ``to_fp``. In ``QF_UFLRA`` a function may take and
return Reals. How its congruence is decided is described in
:doc:`uninterpreted-functions`, under "Real positions".

The C, C++ and Python interfaces build the same terms. The C interface
has ``vc_realType``, ``vc_realConstExprFromStr``, ``vc_realConstExpr``
and ``vc_realPlusExpr`` through ``vc_realGeExpr``. It reads models
through ``vc_getRealModelValue`` (and its ``Numerator``, ``Denominator``
and ``SMTLIBValue`` forms), which return strings the caller frees with
``vc_deleteString``. The probes ``vc_hasQFLRA``, ``vc_hasQFUFLRA``,
``vc_hasRealConstruction`` and ``vc_hasRealIte`` let a program check for
support first. Python has ``Solver.real``, ``Solver.reals``,
``Solver.realval`` and ``RealExpr``, whose model values are exact
``ExactRealValue`` objects. Through the C and C++ interfaces a query may
mix Reals with bit-vectors, arrays and floating point, which SMT-LIB's
logic names cannot express.

How a query is decided
----------------------

**Atoms.** Each Real predicate is normalised to a linear polynomial
compared with a constant, and becomes one Boolean atom of the search.
Predicates over the same polynomial share one row of the tableau, so
``x + y <= 3``, ``x + y >= 5`` and ``x + y < 7`` are three atoms on one
row. ``2x + 2y <= 10`` is a row of its own. Every atom on one row is a
half-line of it, and STP links them with a chain of binary clauses in
threshold order. The SAT solver then knows, without asking the theory,
that ``r <= 3`` rules out ``r >= 5``. That chain is ``ordering_axioms``
in the statistics.

**The exact core.** The core keeps each row as a tableau row over a slack
variable, bounds for each variable (a strict bound carries an
infinitesimal, as Dutertre and de Moura do), and an assignment that it
repairs by pivoting. Pivots are priced by row length and column use, and
after as many pivots as there are variables Bland's rule takes over, so a
repair cannot cycle. An infeasible row is explained by the bounds it rests
on, and that explanation is the conflict clause. Numbers stay in machine
words while they fit. Where the compiler has a 128-bit integer (not MSVC),
a checked 128-bit lane comes next, and after that IMath (see
:doc:`building`).

**Budgets.** Every exact operation is metered against the current
query's budget. A query too big for the budget answers ``unknown`` with
a reason:

.. code-block:: text

    unknown
    (:reason-unknown (incomplete "the exact linear arithmetic solver could not decide this query within its resource budget: exact assertion reached a resource limit"))

That is a limit, not an error. A time limit (``--max-time``) or a
conflict budget (``--max-num-confl``) stops the arithmetic the same way.

**Inside the search.** The first SAT search runs on the Boolean
structure alone. If its assignment satisfies the arithmetic, the query
is decided without the theory ever entering the search. If not, the
atoms are bound to their SAT variables, the ordering clauses are added,
and from the next search on the theory takes part
(``--lra-first-search`` connects it before the first search instead).
Taking part needs a SAT backend that hosts an IPASIR-UP external
propagator (``--lra-theory-propagation``, on by default). Those backends
are CaDiCaL and a CryptoMiniSat built with the interface. As atoms are
assigned the theory checks the partial assignment, and it returns a
conflict as a clause where it arises, rather than after a complete
assignment has been built on top of it. It reports conflicts only. It
does not push implied atoms back to the solver: the ordering clauses
above carry the implications within one row. Measured on the SMT-LIB
QF_LRA and QF_UFLRA sets at twenty seconds, taking part lifted QF_LRA
from 938 to 1018 files solved and QF_UFLRA from 1234 to 1240, with no
answer changed.

A partial check that runs away in big-number arithmetic on a dense
tableau is abandoned, keeping its pivots. After two of those, partial
checks stay off for the rest of the solve, and the propagator still
judges complete assignments. MiniSat hosts no propagator, and neither
does a CryptoMiniSat without the interface or one asked for more than
one thread. There the loop is full-lazy: the SAT solver proposes a
complete assignment, the theory accepts it or returns a conflict, and the
solver goes again.

With the patched CaDiCaL 3.x that STP builds, the theory also picks the
polarity of the SAT solver's next decision on an arithmetic atom, the one
the current assignment already satisfies (``--lra-decision-polarity``).
It is on wherever it is supported. On other backends the option can be
left alone, and asking for it explicitly there is an error.

**The floating-point tier.** By default a double-precision simplex over
the same rows and bounds does the partial checks and proposes models
(``--lra-float-driver``). The exact core is consulted only to certify
what the float tier reports. A float conflict is kept when its weights,
reconstructed as exact rationals, prove it. Otherwise the conflict is
recovered by bounded exact elimination on its support
(``--lra-conflict-recovery``), and failing that it is re-derived by the
exact core. A float model is certified, and repaired over the pinned
bounds if it needs to be. Over 3,037 QF_LRA and QF_UFLRA files (medians
of three), the float tier solved 38 more QF_LRA files at 20 s, left
QF_UFLRA level, and made the typical file a quarter faster, with no
answer disagreement.

The float tableau starts as a substitution tableau. When fill-in makes it
expensive, it switches to a sparse LU basis kept current by Forrest--Tomlin
updates (Forrest and Tomlin, "Updated triangular factors of the basis to
maintain sparsity in the product form simplex method", Mathematical
Programming 2, 1972). Numerical trouble escalates in steps: the basis is
restarted first, then the factorized form takes over, and last the solve
falls back to exact partial checks. The number of fresh factorized tiers
one solve may build is bounded (``--lra-float-promotion-budget``).

A few queries make the float tableau grow without end. Its live nonzeros
climb to tens of times what it was built with, while the exact core
settles the same file in under a second. When the fill exceeds both
``--lra-float-reroute`` times the as-built count (4) and
``--lra-float-reroute-floor`` nonzeros (500,000), the solve stops and the
query is solved again from its start on the exact driver, within the same
deadline. The exact driver then stays in charge for the rest of that
``STPMgr`` or validity checker. Under ``-s`` this prints ``LRA: float
tier blew up; re-solving on the exact driver``.

**Presolve.** Before any atom is made, a query with Real content is
rewritten in five stages, each behind its own option and each on by
default:

- **Substitution** (``--lra-presolve-subst``). A top-level definition
  ``x = t``, with ``x`` not in ``t``, is substituted through the rest of
  the query, and the remaining top-level linear equalities are solved by
  Gaussian elimination. The definitions stay conjoined, so each costs one
  row and nothing else mentions the eliminated variable.
- **Propagation** (``--lra-presolve-propagate``). Each top-level conjunct
  is replaced by its truth value wherever it occurs below the Boolean
  structure, and the constants that exposes are folded, to a small fixed
  point.
- **Unconstrained atoms** (``--lra-presolve-unconstrained``). A variable
  that occurs in one atom only, at one polarity, leaves that atom free
  over the reals. The atom folds to true, and a witness equality that
  realises it is conjoined, so the model stays complete.
- **Rows** (``--lra-presolve-rows``). Top-level inequalities over the
  same canonical polynomial are compared. One implied by a stronger
  sibling is dropped, and a contradictory pair answers ``unsat`` without
  a search.
- **Bounds** (``--lra-presolve-bounds``). Unit conjuncts give each
  variable a bound, and one round derives further bounds through
  multi-variable rows. A variable whose bounds meet is fixed and
  substituted, and contradictory bounds answer ``unsat``. Over the suite
  this stage gained 42 files and lost 19, with no answer changed.

The printed model is checked against the query before presolve as well as
after (``original_formula_checks`` in the statistics). Presolve changes
the formula the exact core sees, so a query near the core's budget can
move either way between an answer and ``unknown``.

**Incremental input.** ``push``, ``pop`` and repeated ``check-sat`` work,
and by default each ``check-sat`` with Real content is solved as a fresh
batch query. ``--lra-incremental-session`` keeps the coordinator, CNF and
SAT solver across the check-sats instead (see the options below).

Checking the answer
-------------------

Every model is evaluated in exact arithmetic against the original query
before it is committed. A model that fails is refused, never printed.
``-d`` (``--check-sanity``) adds STP's ordinary model check on top.
Solving a query with the float tier on and off, or with presolve on and
off, and comparing the answers is therefore a differential test of either
one. The C API flags below exist so that a client can run such
comparisons. Two self-checks re-derive what the core already proves:

``--lra-verify-conflicts``
  Re-derive every conflict certificate independently before the search
  uses it. Off by default. It can only turn a wrong answer into a
  diagnosed failure.

``--lra-verify-canonical``
  Re-derive the canonical form of every exact rational whose construction
  already proves it canonical. Off in the ``stp`` binary. For a library
  caller it is a process-wide default that is on until
  ``LRA_VERIFY_CANONICAL`` turns it off.

``tests/query-files/lra-*.smt2`` run through the lit suite, and again on
each built backend that hosts the propagator, with the float driver on and
off. ``ctest -L lra`` runs the library, frontend and interface tests.

Reading what happened
---------------------

``-s`` prints three lines for a Real query. Presolve reports first:

.. code-block:: text

    LRA presolve: 0 definitions, 0 fixed variables, 0 rows dropped, 0 facts propagated, 3 atoms folded, 0 unconstrained witnessed, bounds_ns=26128, bounds_ops=49

Then comes one JSON object per solve, ``LRA-METRICS {...}``. It has more
than a hundred fields; the ones that answer the usual questions are
these:

- **Size**: ``frontend_symbols``, ``frontend_rows``,
  ``frontend_predicates``, ``ordering_axioms``,
  ``maximum_coefficient_bits``.
- **Search**: ``sat_candidates`` counts complete assignments offered to
  the theory. ``lra_conflicts`` and ``lra_clauses`` count what went back.
  ``partial_conflicts`` counts conflicts found on partial assignments, and
  ``partial_checks_abandoned`` and ``partial_checks_disabled`` show the
  arithmetic guard at work.
- **Float tier**: ``float_checks``, ``float_pivots``, ``float_check_ns``;
  ``float_certified`` and ``float_certificate_failed`` for its conflicts;
  ``conflict_recoveries``; and ``float_restarts``, ``float_factorized``
  and ``float_promotions`` for the escalation steps.
- **Exact core**: ``exact_checks``, ``exact_pivots``, ``bland_pivots``,
  ``core_rebuilds``.
- **Numbers**: ``number_profile.big_operations`` counts operations that
  went to IMath. ``maximum_numerator_bits`` and
  ``maximum_denominator_bits`` give the widest value seen.
- **Model**: ``models_committed``, ``original_formula_checks``,
  ``model_verifier_ns``.
- **Outcome**: ``interruptions``, ``resource_stops`` and
  ``internal_errors``. A non-empty ``failure`` names what stopped the
  solve.

A query with uninterpreted functions also prints ``UF lazy congruence:
rounds=... lemmas=... expanded=... restarts=...``, and ``extensions`` in
the JSON counts the lemma rounds that extended the running solve in place.
``Query phases:`` gives the wall-clock split, with the arithmetic's
teardown as ``lra_cleanup_ns``.

Options
-------

Every option below is a verdict-preserving control. Changing it can make
a query faster, slower or ``unknown``, but a sat/unsat answer stays the
same. Options that take ``auto``, ``on`` or ``off`` also accept ``1``,
``0``, ``true`` and ``false``.

Search and the float tier
~~~~~~~~~~~~~~~~~~~~~~~~~

``--lra-theory-propagation`` (on)
  Take part in the SAT search on a backend that hosts a propagator, as
  described above. Off, every backend runs the full-lazy loop.

``--lra-decision-polarity`` (on where supported)
  Pick the polarity of arithmetic decisions. It needs
  ``--lra-theory-propagation`` and the patched CaDiCaL. ``=0`` restores
  the backend's own polarity, and an explicit ``=1`` without support is
  an error.

``--lra-float-driver`` (on)
  Drive partial checks with the double-precision simplex. ``=0`` uses the
  exact core alone.

``--lra-conflict-recovery`` (on)
  Recover a rejected float conflict's weights by bounded exact
  elimination before re-deriving it on the exact core.

``--lra-float-promotion-budget`` (4)
  Fresh factorized float tiers one solve may build after the double tier
  trips its infinitesimal cap. Past it the solve continues on exact
  partial checks; ``0`` is unbounded. One solve was measured building
  18,094 of them unbounded.

``--lra-float-reroute`` (4), ``--lra-float-reroute-floor`` (500000)
  The fill multiple and the absolute live-nonzero floor that together
  trigger a re-solve on the exact driver. ``--lra-float-reroute=0``
  disables the reroute, and ``--lra-float-reroute-floor=0`` removes the
  floor. The ratio alone trips on small healthy problems: a
  corpus scan found 134 files past ratio 8, and 131 of them solved on the
  float tier anyway, all under 400,000 live nonzeros, while the real
  blow-ups reach millions.

``--lra-separate-model-values`` (auto)
  Before a model is published, move variables within the slack their
  bounds leave, so that fewer of them share a value by accident. Only the
  lazy congruence round is misled by such a coincidence, so ``auto``
  runs this when the query has a Real-position function. On QF_UFLRA it
  was worth two solves and 11.8% of PAR-2; on QF_LRA it gained nothing.

Presolve
~~~~~~~~

The five stages above are ``--lra-presolve-subst``,
``--lra-presolve-propagate``, ``--lra-presolve-unconstrained``,
``--lra-presolve-rows`` and ``--lra-presolve-bounds``, all on by default.

``--lra-presolve-rounds`` (1)
  Presolve rounds, from 1 to 8, stopping early at a fixed point. More
  than one is experimental.

``--lra-presolve-subst-growth`` (0), ``--lra-presolve-subst-work`` (1000000)
  A query-wide allowance for the new DAG nodes and child links that
  substitution may create, and the work it may spend while that allowance
  is in force. Exhausting either keeps the remaining equations as they
  are. The default growth of ``0`` leaves substitution unguarded.

``--lra-presolve-monotone`` (off), ``--lra-presolve-monotone-work`` (1000000)
  Experimental. Eliminate a variable that every atom constrains in the
  same direction, and recover its value exactly before the model check.
  The work cap keeps the input unchanged when it runs out.

``--lra-model-reconstruction`` (auto)
  Eliminate affine definitions and reconstruct them in the model. ``auto``
  does so only for the ReLU proposals below, and ``on`` also does it for
  ordinary queries.

Exact core
~~~~~~~~~~

``--lra-direct-bounds`` (0)
  Experimental. Bound a single variable directly instead of through an
  auxiliary row: ``1`` for rows that are the variable itself, ``2`` for
  any single-variable row.

``--lra-singleton-ordering`` (off)
  Experimental. Add ordering clauses across all the scaled bounds of one
  variable, not only within one row.

``--lra-soi`` (off), ``--lra-early-conflicts`` (off)
  Experimental. Repair by a bounded sum-of-infeasibilities search (King,
  Barrett and Dutertre, "Simplex with Sum of Infeasibilities for SMT",
  FMCAD 2013), and scan the rows a repair touches for a conflict before
  pivoting.

``--lra-float-dormant-rows`` (off), ``--lra-float-dormant-min-cells`` (0)
  Experimental. Keep float-tier rows that have no asserted bound out of
  the tableau until their first bound, optionally only rows at least this
  many cells wide.

``--lra-dense-recovery`` (off)
  Experimental. Work budgets that scale with density, and a bounded
  floating-point recovery before falling back to exact checks.

``--lra-first-search`` (off)
  Experimental. Bind the atoms, add the ordering clauses and connect the
  propagator after CNF generation, before the first SAT search, instead
  of after the first candidate.

ReLU networks and HiGHS
~~~~~~~~~~~~~~~~~~~~~~~

A query that encodes a neural network asserts ReLUs as disjunctions such
as ``(or (and (<= x 0) (= y 0)) (and (>= x 0) (= y x)))``. When STP
recognises these at top level, it propagates exact intervals through the
network and its affine definitions, and settles the ReLUs whose phase the
intervals decide (``--lra-relu-bounds``, ``auto``). Recognition is
bounded, runs on every Real query and acts only on this shape. When it
fires, substitution, unconstrained and monotone elimination are skipped
for that query to keep the network sparse. ``--lra-boolean-bounds`` (on)
adds interval hulls across asserted Boolean alternatives, and
``--lra-relu-cases`` (off, ``--lra-relu-cases-seconds`` 60) refutes
property alternatives one input box at a time.

`HiGHS <https://highs.dev>`__ is an optional LP and MIP engine, built in
with ``-DENABLE_HIGHS=ON`` (see :doc:`building`). STP certifies exactly
whatever it takes from HiGHS: a bound needs a dual certificate that checks
in rationals, and a model is checked like any other. In a build without
it, the options that need it are refused at parse time with a message
naming the CMake option.

``--lra-relu-lp`` (auto)
  Tighten uncertain ReLU bounds by LP, with exact dual certificates, and
  propose models. ``auto`` runs on eligible networks only, for at most
  ``--lra-relu-auto-seconds`` (1). ``on`` runs the full search, bounded by
  ``--lra-relu-lp-rounds`` (8), ``--lra-relu-lp-seconds`` (60) and
  ``--lra-relu-lp-call-seconds`` (2) per LP. It needs HiGHS; ``--lra-lp-screen``
  (on) skips certificates unlikely to help, and ``--lra-lp-partial`` (on)
  still checks proposals from LPs that did not finish.

``--lra-relu-branch`` (off)
  A relaxation-guided search over ReLU phases, returning exactly checked
  conditional conflicts as clauses. Bounded by ``--lra-relu-branch-nodes``
  (128) and ``--lra-relu-branch-seconds`` (60). ``--lra-relu-property-branches``
  (on) includes the property's own alternatives. It needs HiGHS.

``--lra-replay-screen`` (on)
  Replay a candidate input through the network in floating point before
  reconstructing its model exactly, and drop the ones that cannot work.

``--lra-highs-lp``, ``--lra-highs-mip``, ``--lra-highs-replay``, ``--lra-highs-cuts`` (all off)
  General HiGHS proposals over the original rows: LP bases and rays;
  models for variables asserted to be 0 or 1; replay of binary branches as
  conditional conflicts (``--lra-highs-replay-nodes``, 128); and root cuts
  rebuilt exactly (``--lra-highs-cut-limit``, 64). The cuts need
  ``-DENABLE_HIGHS_CUT_LOG=ON``. ``--lra-highs-seconds`` (5) is their
  shared time budget. MIP is off because it paid for itself nowhere: on
  the network queries it applies to, it solved the same 6 of 20 in the
  same time with it on or off.

Incremental sessions
~~~~~~~~~~~~~~~~~~~~

``--lra-incremental-session`` (off)
  Keep one Real solve across the ``check-sat`` calls of an SMT-LIB script
  that uses ``push``. The coordinator, CNF and SAT solver persist with
  their learned clauses; a pushed level is added under an activation
  literal of its own and retracted on ``pop``. The exact core is still
  rebuilt when the stack changes. Only stacks of Boolean and Real terms
  engage it. Uninterpreted functions, bit-vectors, arrays, floating
  point, ``distinct`` and ``check-sat-assuming`` take the batch path. A
  check that spends its time or conflict budget answers ``unknown``, and
  the next check starts a new session. It is off because it is sound but
  not yet faster: on the many-check QF_LRA incremental files it is slower
  than the batch path.

``--lra-persistent-state`` (off)
  Inside that session, also keep the arithmetic registrations and bases
  across checks. This implies the session.

Search-state experiments
~~~~~~~~~~~~~~~~~~~~~~~~

These batch-query controls vary arithmetic state, row insertion order and
SAT search history independently of one another. All four default to
``0``.

* ``--lra-extension-mode=0`` chooses automatically: ordinary batch UF
  refinement rebuilds the arithmetic context. ``1`` always extends in place.
  ``2`` always rebuilds the context. ``3`` extends in place, then resets both
  arithmetic assignments and bases, preserving all allocated IDs and their
  interleaved column/row order. SAT search persists in each of these modes.
* ``--lra-row-order=0`` retains registry order. ``1`` reverses new arithmetic
  rows, ``2`` inserts sparse rows first, and ``3`` inserts dense rows first.
  Ties retain registry order. This changes construction of the exact and
  floating tableaux; it preserves Boolean atom creation and CNF order.
  Each later extension orders its newly added rows using the same policy.
* ``--lra-extension-restart-float-basis=1`` restores the advisory slack basis
  after extensions, retaining structural-variable assignments and IDs. The
  exact tier is retained. Mode ``3`` takes precedence and resets assignments
  in both tiers. Experimental resets do not consume numerical-recovery
  budgets; their work is measured separately.
* ``--lra-extension-restart-sat=1`` copies the Boolean formula into a fresh
  CaDiCaL instance after each permanent extension. CaDiCaL copies irredundant
  clauses, units, options, preprocessing state and witness reconstruction;
  redundant learned clauses, activities and saved phases are discarded.
  This keeps the formula's models and external variable identities, but
  does not undo preprocessing or replay the original clause order. Solve
  assumptions are reapplied normally and the query deadline is retained.

Nondefault controls require batch solving. Combining one with a session
option is rejected when the solve starts, and the query reports an error.
SAT search reset requires CaDiCaL with factoring disabled
(``--cadical-factor=off``). The controls still use exact model and conflict
checking. ``context_reuses``, ``arithmetic_state_resets``,
``float_basis_resets`` and ``sat_search_resets`` show which paths ran.
``total_exact_pivots``, ``total_float_checks``, ``total_float_pivots``,
``total_float_check_ns`` and ``total_float_sync_ns`` include retired
arithmetic contexts as well as the final context. The other work fields
describe the final context only, and can omit work when rebuilding is
enabled.

C API
-----

``vc_setInterfaceFlags`` sets the LRA controls a library caller is most
likely to vary. The ordinals are fixed and appended after the
floating-point abstraction's; ``param_value`` is nonzero for on and zero
for off.

.. list-table::
   :header-rows: 1
   :widths: 40 10 50

   * - Flag
     - Value
     - Option
   * - ``LRA_THEORY_PROPAGATION``
     - 61
     - ``--lra-theory-propagation``
   * - ``LRA_VERIFY_CONFLICTS``
     - 62
     - ``--lra-verify-conflicts``
   * - ``LRA_VERIFY_CANONICAL``
     - 63
     - ``--lra-verify-canonical``; process-wide, read when each budget is created
   * - ``LRA_PRESOLVE_SUBST``
     - 64
     - ``--lra-presolve-subst``
   * - ``LRA_PRESOLVE_BOUNDS``
     - 65
     - ``--lra-presolve-bounds``
   * - ``LRA_PRESOLVE_ROWS``
     - 66
     - ``--lra-presolve-rows``
   * - ``LRA_PRESOLVE_PROPAGATE``
     - 67
     - ``--lra-presolve-propagate``
   * - ``LRA_PRESOLVE_UNCONSTRAINED``
     - 68
     - ``--lra-presolve-unconstrained``
   * - ``LRA_FLOAT_DRIVER``
     - 69
     - ``--lra-float-driver``
   * - ``LRA_INCREMENTAL_SESSION``
     - 70
     - ``--lra-incremental-session``; only the SMT-LIB ``check-sat`` path reads it, ``vc_query`` does not

A Real constructor that exceeds the exact-arithmetic budget returns NULL
through the registered error handler, and a query that exceeds it answers
``unknown``.
