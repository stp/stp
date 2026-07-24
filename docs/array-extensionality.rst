Array extensionality
====================

By default STP implements the *non-extensional* theory of arrays: it can
reason about array elements (``select``/``store``), but not about arrays
as whole values. An equality between two array terms is rejected with a
warning.

With the ``--array-equality`` option STP decides the quantifier-free
*extensional* theory of arrays: equality and ``distinct`` between array
terms become first-class atoms. The implementation follows

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

With the option enabled:

* ``(= a b)`` and ``(distinct a b)`` over array terms are decided, as is
  equality involving ``store`` chains and array-valued ``ite``;
* ``(get-model)`` prints each array as a valid nullary ``define-fun``
  whose body is a constant-zero array with the observed writes stored on
  top, in ascending index order — the model replays in any conforming
  SMT-LIB2 solver;
* ``vc_getCounterExampleArray`` returns one entry per concrete index in
  ascending index order;
* nullary array-sorted ``define-fun`` is accepted by the SMT-LIB2
  parser;
* array-valued ``(get-value ...)`` is rejected as unsupported (use
  ``(get-model)``).

Without the option, STP behaves exactly as it did before the feature
existed — output, accepted language, and model APIs included. A test
(``default-off-capi-baseline-differential``) builds the pre-feature
baseline from git history and compares the observable behavior byte for
byte.

Limitations: arrays of arrays are not supported (STP's sort system has
no nested array sorts), and there is no constant-array
(``as const``) input syntax.

How it works
------------

The procedure is an abstraction-refinement loop around STP's existing
bit-vector core (the paper's ``DP_A``, with STP's bit-blaster and SAT
solver playing ``DP_B``):

1. **Abstraction.** Every equality between array terms is replaced — at
   node-creation time, in the shared node factory — by a fresh Boolean
   *abstraction variable*, so no array equality ever reaches STP's
   simplifier, array transformer, or bit-blaster. Reads are abstracted
   by fresh variables by STP's existing machinery.

   One shape skips abstraction entirely: a chain of writes equated
   with its own base array (the frame condition ``store(a,i,v) = a``
   and its nestings) is solved by rewriting into read equalities over
   the base, each guarded by disequality with the indices of the
   writes that shadow it. Such an equality contributes nothing to the
   refinement loop at all.

2. **Preprocessing** (paper §4). For each abstracted equality ``a = b``
   a fresh *witness index* λ and two *virtual reads* ``a[λ]``, ``b[λ]``
   are created, with the constraint ``a = b ∨ a[λ] ≠ b[λ]``: if the SAT
   solver makes the equality false, the two arrays must visibly differ
   at λ (axiom A4′). Array-valued ``ite(c, a, b)`` connected to an
   equality is replaced by a fresh array ``d`` with ``c → d = a`` and
   ``¬c → d = b`` (paper §4.1). Every index and value that could appear
   in a future lemma is given a named variable inside the initial
   formula, so refinement lemmas can later be encoded over SAT
   variables that already exist.

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
   through fresh definitional literals) and added to the incremental
   SAT solver; the loop re-solves. Each lemma permanently excludes the
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
