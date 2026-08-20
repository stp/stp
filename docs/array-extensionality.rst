Array extensionality
====================

STP reasons about array elements (``select``/``store``) always, and
about arrays as whole values with the ``--array-equality`` option: it
then decides the quantifier-free *extensional* theory of arrays, in
which equality and ``distinct`` between array terms are first-class
atoms. Without the option an equality between two array terms is
refused, with an error, at the point the term is built -- except a
syntactically reflexive one, which the simplifying node factory folds to
true before the rejection is reached.

The implementation is an STP-specific integration of the
lemmas-on-demand procedure of

    Robert Brummayer and Armin Biere,
    *Lemmas on Demand for the Extensional Theory of Arrays*,
    Journal on Satisfiability, Boolean Modeling and Computation 6
    (2009), 165--201.

Usage
-----

Command line::

    stp --array-equality file.smt2

C API: call ``vc_setFlag(vc, 'x')`` before constructing any equality
between whole arrays.
The option controls whether construction of the dedicated opaque
``ARRAY_EQ`` node is permitted; its abstraction is deferred until the
completed query reaches the solver.

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
  whose body is a constant default cell with the observed writes stored
  on top, in ascending index order — the model replays in any conforming
  SMT-LIB2 solver. This form is used whenever the option is on, even for
  a query containing no array equality; only with the option off does
  the pre-feature array printer run;
* ``vc_getCounterExampleArray`` returns one entry per concrete index in
  ascending index order;
* array-valued ``(get-value ...)`` is rejected as unsupported (use
  ``(get-model)``). This is not conditional on the option: an array has no
  value spelling in a valuation pair either way.

Nullary array-sorted ``define-fun`` is accepted by the SMT-LIB2 parser
whether or not the option is on: such a definition is a pure name for its
body, and benchmarks use them without any whole-array equality in sight.

Without the option, STP decides exactly what it decided before the
feature existed, with one deliberate exception: an equality between whole
array terms is now refused rather than warned about. It was never
decided -- nothing eliminates the array-sorted operands, so the atom
reached the solver unconstrained and the verdict could be wrong, and a
build with assertions aborted instead of answering. Both behaviours
reproduce on STP releases predating this feature. The documented C API
surface is pinned by an opt-in test
(``default-off-capi-baseline-differential``, enabled with
``-DTEST_BASELINE_DIFFERENTIAL=ON``), which builds the upstream commit
this branch was last merged with from git history and compares every
observation of an identical C API driver — verdicts, model values, every
counterexample-array entry, stdout, stderr and exit status — across the
two builds. Holding upstream fixed on both sides is what makes the
difference attributable to this feature; a baseline frozen further back
would also collect every unrelated upstream change made since. The
driver canonicalizes the entry order before comparison: the default-off
API does not specify one, and the legacy order comes from an unordered
map keyed by internal node-creation IDs. One diagnostic text
deliberately differs from the baseline and sits outside that comparison:
whole-array equality is refused with an error naming the option, where
the baseline warned and continued (pinned by a lit test). One
behavioral corner also deliberately differs: when the
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

1. **Opaque construction and solve-boundary lowering.** Construction of
   an equality between whole arrays produces a dedicated, near-opaque
   ``ARRAY_EQ`` node whose operands remain visible. The node factory folds
   the shapes that are decidable on sight -- reflexivity, two writes to
   the same index, and an if-then-else against one of its own branches --
   and leaves everything else alone. Function, ``let`` and query
   substitution therefore specialize the operands normally. Once the
   complete query has been assembled, a DAG traversal replaces every
   reachable ``ARRAY_EQ`` with a fresh Boolean *abstraction variable* and
   creates
   its witness record. Repeated or operand-swapped pairs reuse one record
   within that solve, and a reflexive equality folds to true. Records,
   proxies and witnesses are solve-local and are rebuilt for the next
   query; only the opaque public AST persists. No ``ARRAY_EQ`` reaches the
   array transformer or the bit-blaster.

   Two preprocessing passes deliberately run *before* that lowering, and
   are the only points in the solve that see an ``ARRAY_EQ`` at all.
   Equality propagation goes first, so that a definitional equality
   substitutes its symbol operand away and never reaches abstraction.
   Unconstrained-variable elimination goes second, because an equality
   with an unconstrained operand is a free Boolean and settles there
   rather than costing a record, a witness pair and a refinement loop.
   Afterwards the operands sit under witness reads, and the unconstrained
   array rules turn themselves off.

   One shape skips abstraction entirely: a chain of writes equated
   with its own base array (the frame condition ``store(a,i,v) = a``
   and its nestings) is solved by rewriting into read equalities over
   the base, each guarded by disequality with the indices of the
   writes that shadow it. Such an equality contributes nothing to the
   refinement loop at all.

   Array-valued ``ite(c, a, b)`` is *not* abstracted at all: it is
   built as an ordinary node and stays one, and the consistency checker
   reasons about it directly (see stage 3).

2. **Solve-time preparation.** Each current-root equality ``a = b``
   lowered in this solve
   carries a fresh *witness index* λ and two *virtual reads* ``a[λ]``,
   ``b[λ]``, with the constraint ``a = b ∨ a[λ] ≠ b[λ]``: if the SAT
   solver makes the equality false, the two arrays must visibly differ
   at λ (axiom A4′, the paper's preprocessing step 1). These are
   conjoined onto the formula before STP's ordinary simplification,
   and the equality operands are recovered from them afterwards in
   their simplified form. Each anchor remains a plain read even when its
   operand is an array-valued if-then-else, because read distribution is
   suppressed while the procedure is active. Every index and value that
   could appear in a future lemma
   is given a named variable inside the initial formula, so refinement
   lemmas can later be encoded over SAT variables that already exist.

   Once any equality is active, the checker owns the complete array graph
   reachable from the prepared formula, rather than a syntactic cone
   around the equality operands. Every surviving array-valued
   ``ite(c, a, b)`` in that graph has its condition *reified*: a fresh
   Boolean symbol ``n_c`` with
   ``n_c ↔ c``. The checker decides which branch of an if-then-else is
   live from ``σ(n_c)``, and that has to be the value the bit-blasted
   circuit took — re-deriving it from the counterexample is how a
   scalar name comes to disagree with the term it stands for, and here
   it would make the wrong branch live and certify a model that does
   not satisfy the if-then-else axiom. The same symbol is what a lemma
   premise names, since encoding needs one fully encoded literal per
   Boolean atom. Reads are not distributed over these if-then-elses,
   by the simplifier or by the array transformer: the structure and
   its read-abstraction variables have to reach the checker intact.

   These two stages realize the transformations of the paper's §4 and
   §5 in an STP-specific order: construction preserves a durable opaque
   equality; the fully expanded solve root is then lowered to solve-local
   proxies and witnesses; ordinary preprocessing rewrites the result;
   and operand recovery plus complete-graph freezing happen immediately
   before array transformation. Opacity permits function specialization
   to finish before lowering while still ensuring that ordinary STP
   processing never sees an array equality.

3. **Consistency checking** (paper §7, ``lib/Extensionality/``). When
   the SAT solver produces a satisfying assignment σ, a pure checker
   decides whether σ can be extended to a real array model. It seeds
   every access at its own array (rule *I*; writes are treated as reads
   of themselves per §11.4, so write congruence needs no extra
   constraints), then propagates accesses to a fixed point: down
   through and up over writes whose index differs from the access
   index under σ (rules *D*/*U*, axiom A3), across array equalities
   that σ makes true (rules *R*/*L*), and between an array-valued
   if-then-else and whichever branch σ selects (rules *T-down*/*T-up*).
   Two accesses meeting at one array
   with equal concrete indices but different values violate read
   congruence (rule *C*, axiom A1).

   The *T* rules are the direct integration §4.1 mentions but declines
   to present ("in principle, our approach supports a direct
   integration of if-then-else on terms of sort Array without rewriting
   it up front"). They are *R*/*L* with the equality proxy replaced by
   the condition literal and the destination chosen by σ rather than
   fixed by the edge, and their soundness case is Lemma 8.1's *R* case
   with axiom A4 replaced by the if-then-else axiom. The model
   construction of §9 needs one new obligation, the analogue of
   Proposition 9.4 — and only its *positive* half, because the
   if-then-else axiom is a pair of implications rather than a
   biconditional: nothing ever requires an if-then-else to *differ*
   from a branch, so no witness index and no virtual reads are needed
   for one. Exactly one branch is live per candidate, so unlike an
   array equality there is no proxy left unconstrained for the SAT
   solver to guess and the checker to refute.

   The alternative §4.1 does present — rewriting ``ite(c,a,b)`` up
   front into a fresh array ``d`` with ``c → d = a`` and ``¬c → d = b``
   — is what this replaced. It charges two array equalities, two
   witness indices and four virtual reads per if-then-else where the
   direct rules charge one Boolean literal, so it is worse on the
   paper's own bound (Proposition 10.1), and each of its two proxies is
   unconstrained under one of the two assignments of the condition. Its cost also
   grew with nesting depth on array if-then-else under an equality, where
   the direct rules are flat.

   Per §11.2 the checker keeps one
   representative access per concrete index of each array, keyed by its
   index value: congruence is a single lookup, and an access arriving
   with the same index and value as its representative is dropped
   without further propagation.

4. **Lemmas on demand** (paper §8). A conflict yields the lemma

   .. code-block:: text

      index(x) = index(y) ∧ ⋀ path write-index disequalities
                          ∧ ⋀ crossed array equalities
                          ∧ ⋀ crossed if-then-else conditions
        →  value(x) = value(y)

   which is false in the candidate σ. Propagation paths are as short as
   the pass can make them (the minimization of §11.1): seeding every
   access before the fixed point starts makes the FIFO work list
   breadth-first per access, so the arrival that fires a conflict is the
   earliest — shortest — one. Because the pass continues past a
   conflict rather than stopping at it, that is exact for the first
   conflict of a pass and best-effort afterwards: an arrival that
   conflicts is not queued onward, so a later conflict uses the shortest
   route still open to it, and a pair that could only have met at an
   earlier conflict site waits for a later refinement round. The lemma
   is encoded as clauses over
   the SAT variables of the already-encoded names (equalities reified
   through fresh definitional literals); an atom the simplifier can
   decide from its defining terms — write indices that are distinct
   constant offsets from one pointer are the common case — is dropped
   at encoding time instead of becoming an equality circuit the SAT
   solver would have to search through, on whichever side of the atom
   the structural verdict permits. The clause is added to the
   incremental SAT solver; the loop re-solves. Each lemma permanently excludes the
   assignment that produced it, so the loop terminates.

5. **Models.** When the checker finds no conflict, the fixed point of
   its propagation defines each array's observed contents; unobserved
   indices take a single default cell, which is zero except for an array
   of ``RoundingMode`` elements, where zero is not a mode at all and the
   default is ``RNE``. These observations — including the witness
   indices of false equalities — feed the model printer and the
   programmatic model APIs.

When at least one equality is active, the consistency checker owns the
complete reachable array graph and directly abstracts every read in it.
STP's legacy lazy read refinement is not entered during such a solve. This
single ownership boundary avoids candidates whose scalar dependencies
crossed the former checker/legacy partition. When no equality is active,
the extensionality checker remains dormant and STP's legacy array path runs
unchanged. An active candidate is reported satisfiable only when both the
array consistency check and STP's ordinary model evaluation pass on the
same assignment.
