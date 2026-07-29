Array extensionality
====================

By default STP implements the *non-extensional* theory of arrays: it can
reason about array elements (``select``/``store``), but not about arrays
as whole values. An equality between two array terms is rejected with a
warning.

With the ``--array-equality`` option STP decides the quantifier-free
*extensional* theory of arrays: equality and ``distinct`` between array
terms become first-class atoms. The implementation is an STP-specific
integration of the lemmas-on-demand procedure of

    Robert Brummayer and Armin Biere,
    *Lemmas on Demand for the Extensional Theory of Arrays*,
    Journal on Satisfiability, Boolean Modeling and Computation 6
    (2010), 165--201.

Usage
-----

Command line::

    stp --array-equality file.smt2
    stp_simple --array-equality file.smt2

C API: call ``vc_setFlag(vc, 'x')`` immediately after creating the
validity checker, *before any term is created* — array equalities are
abstracted at node-creation time, so enabling the option later is
unsupported.

Python API: create the solver with ``stp.Solver(array_equality=True)``.
Arrays are built with ``Solver.array(name, index_width, value_width)``,
read with ``a[i]``, written with ``a.store(i, v)``, and compared whole
with ``==``/``!=``; ``ArrayExpr.model()`` returns an array's entries in
a satisfying assignment, in ascending index order. Comparing whole
arrays on a solver created without the option raises ``RuntimeError``.

With the option enabled:

* ``(= a b)`` and ``(distinct a b)`` over array terms are decided, as is
  equality involving ``store`` chains and array-valued ``ite``;
* ``(get-model)`` prints each array as a valid nullary ``define-fun``
  whose body is a constant-zero array with the observed writes stored on
  top, in ascending index order — the model replays in any conforming
  SMT-LIB2 solver. This form is used whenever the option is on, even for
  a query containing no array equality; only with the option off does
  the pre-feature array printer run;
* ``vc_getCounterExampleArray`` returns one entry per concrete index in
  ascending index order;
* nullary array-sorted ``define-fun`` is accepted by the SMT-LIB2
  parser;
* array-valued ``(get-value ...)`` is rejected as unsupported (use
  ``(get-model)``).

Without the option, STP decides exactly what it decided before the
feature existed. The C API surface is pinned byte for byte: an opt-in
test (``default-off-capi-baseline-differential``, enabled with
``-DTEST_BASELINE_DIFFERENTIAL=ON``) builds the pre-feature baseline
from git history and compares every observation of an identical C API
driver — verdicts, model values, counterexample-array entries and
their order, stdout, stderr, exit status — across the two builds. Two
diagnostic texts deliberately differ from the baseline and sit outside
that comparison: the parser's array-extensionality warning now names
the option (its full text and once-per-run latch are pinned by a lit
test), and ``stp_simple``'s usage error mentions the flag it newly
accepts. One behavioral corner also deliberately differs: when the
soft timeout expires while lazy refinement is still undecided, the
solve now reports a timeout where it previously aborted with an
internal error.

Limitations: arrays of arrays are not supported (STP's sort system has
no nested array sorts), and there is no constant-array
(``as const``) input syntax.

How it works
------------

The procedure is an abstraction-refinement loop. As a whole it plays
the paper's ``DP_A``, the decision procedure for the theory of arrays;
STP's existing bit-blaster and SAT solver provide ``DP_B``, the solver
for each abstracted candidate formula:

1. **Construction-time registration and abstraction.** Each equality
   between a new canonical pair of array terms is replaced — at
   node-creation time, in the shared node factory — by a fresh Boolean
   *abstraction variable*; repeated or operand-swapped requests reuse
   that variable, and a reflexive equality folds to true. No array
   equality ever reaches STP's simplifier, array transformer, or
   bit-blaster. The registry also eagerly records, per equality, the
   witness constraints that the next stage places into the formula.
   Reads are abstracted by fresh variables by STP's existing machinery.

   One shape skips abstraction entirely: a chain of writes equated
   with its own base array (the frame condition ``store(a,i,v) = a``
   and its nestings) is solved by rewriting into read equalities over
   the base, each guarded by disequality with the indices of the
   writes that shadow it. Such an equality contributes nothing to the
   refinement loop at all.

2. **Solve-time preparation.** Each registered equality ``a = b``
   carries a fresh *witness index* λ and two *virtual reads* ``a[λ]``,
   ``b[λ]``, with the constraint ``a = b ∨ a[λ] ≠ b[λ]``: if the SAT
   solver makes the equality false, the two arrays must visibly differ
   at λ (axiom A4′, the paper's preprocessing step 1). These are
   conjoined onto the formula before STP's ordinary simplification,
   and the equality operands are recovered from them afterwards in
   their simplified form. Array-valued ``ite(c, a, b)`` connected to
   an equality is replaced by a fresh array ``d`` with ``c → d = a``
   and ``¬c → d = b`` (paper §4.1). Every index and value that could
   appear in a future lemma is given a named variable inside the
   initial formula, so refinement lemmas can later be encoded over SAT
   variables that already exist.

   These two stages realize the transformations of the paper's §4,
   §4.1 and §5 in an STP-specific order: the paper presents array-ITE
   elimination and witness preprocessing *before* formula abstraction,
   while STP mints equality proxies and witness records eagerly at
   construction, then recovers and prepares their array operands
   during the solve.

3. **Consistency checking** (paper §7, ``lib/Extensionality/``). When
   the SAT solver produces a satisfying assignment σ, a pure checker
   decides whether σ can be extended to a real array model. It seeds
   every access at its own array (rule *I*; writes are treated as reads
   of themselves per §11.4, so write congruence needs no extra
   constraints), then propagates accesses to a fixed point: down
   through and up over writes whose index differs from the access
   index under σ (rules *D*/*U*, axiom A3), and across array equalities
   that σ makes true (rules *R*/*L*). Two accesses meeting at one array
   with equal concrete indices but different values violate read
   congruence (rule *C*, axiom A1). Per §11.2 the checker keeps one
   representative access per concrete index of each array, hashed by
   index value: congruence is a single probe, and an access arriving
   with the same index and value as its representative is dropped
   without further propagation.

4. **Lemmas on demand** (paper §8). A conflict yields the lemma

   .. code-block:: text

      index(x) = index(y) ∧ ⋀ path write-index disequalities
                          ∧ ⋀ crossed array equalities
        →  value(x) = value(y)

   which is false in the candidate σ. Both propagation paths are
   shortest paths (the minimization of §11.1): seeding every access
   before the fixed point starts makes the FIFO work list breadth-first
   per access, so the arrival that fires a conflict is the earliest —
   shortest — one. The lemma is encoded as clauses over
   the SAT variables of the already-encoded names (equalities reified
   through fresh definitional literals); an atom the simplifier can
   decide from its defining terms — write indices that are distinct
   constant offsets from one pointer are the common case — is dropped
   at encoding time instead of becoming an equality circuit the SAT
   solver would have to search through. The clause is added to the
   incremental SAT solver; the loop re-solves. Each lemma permanently excludes the
   assignment that produced it, so the loop terminates.

5. **Models.** When the checker finds no conflict, the fixed point of
   its propagation defines each array's observed contents; unobserved
   indices default to zero. These observations — including the witness
   indices of false equalities — feed the model printer and the
   programmatic model APIs.

The consistency checker interleaves with STP's ordinary lazy read
refinement: arrays connected to an abstracted equality are owned by the
checker (STP's Ackermann-style read axioms are skipped for them), all
other arrays are refined exactly as before. A candidate is reported
satisfiable only when STP's own model evaluation and the array
consistency check both pass on the same assignment.
