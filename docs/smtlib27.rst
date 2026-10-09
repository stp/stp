SMT-LIB 2.7 compatibility
=========================

STP targets the `SMT-LIB 2.7 reference, release 2025-02-05
<https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf>`__
for its supported quantifier-free theories. This is the target of the
compatibility work tracked in `issue 500
<https://github.com/stp/stp/issues/500>`__. It is not a claim that STP
implements every SMT-LIB theory or every feature added in 2.7.

The command-line reader and the API's ``EXECUTE`` and ``PARSE_ONLY`` script
modes enforce the command protocol. The API's ``DECLARE_AND_ASSERT`` mode
also accepts fragments in an existing solver context; it does not require
a complete, standalone SMT-LIB script.

Writing a script
----------------

For portable scripts, place options that control the products of solving
before ``set-logic``, as the specification prescribes. STP also accepts
them after ``set-logic``, like cvc5 and Bitwuzla. For example:

.. code-block:: lisp

    (set-option :produce-models true)
    (set-option :produce-assignments true)
    (set-logic QF_BV)
    (set-info :smt-lib-version 2.7)
    (define-sort Byte () (_ BitVec 8))
    (declare-const x Byte)
    (assert (! (= x #x2a) :named answer))
    (check-sat)
    (get-value (x))
    (get-assignment)
    (exit)

An explicit ``set-logic`` precedes declarations, assertions and checks,
and may occur only once between resets. If omitted, STP selects ``ALL``
when the first such command needs a logic, like the default frontends of
cvc5 and Bitwuzla. ``ALL`` selects STP's supported
quantifier-free theories together. Array logics enable extensional array
equality automatically; UF logics enable uninterpreted functions. See
:doc:`index` for the accepted logic names and :doc:`linear-real-arithmetic`
for the linear arithmetic fragment.

A model query requires the relevant option and a current satisfiable
context. An assertion, declaration, nonzero ``push`` or ``pop``, or
``reset-assertions`` ends that context: check again before querying a
model. Definitions and zero-level stack operations preserve the model;
they add no constraints or unconstrained symbols. ``reset`` returns to
the initial state, including default options
and output channels. ``reset-assertions`` preserves options and the logic,
and retains declarations only when ``:global-declarations`` is true.

Implemented language and protocol features
------------------------------------------

.. list-table::
   :header-rows: 1
   :widths: 30 70

   * - Area
     - Behavior
   * - Declarations and definitions
     - ``declare-const``, ``declare-fun``, ``define-const`` and
       nonrecursive ``define-fun``; nullary uninterpreted sorts in logics
       that support them; scoped, parameterized ``define-sort`` aliases
       with simultaneous substitution of their parameters.
   * - Terms
     - Simultaneous ``let`` bindings, lexical shadowing of user names,
       sort-qualified identifiers ``(as f Sort)``, general attributes and
       ``:named`` inline definitions. As a compatibility extension, local
       binders may also shadow theory names; top-level theory names remain
       protected. A qualification checks the result sort; it does not
       convert a value.
   * - Operator attributes
     - N-ary Core connectives and equality, including Real equality;
       pairwise ``distinct``; right-associative implication; supported
       bit-vector operators with their associative syntax. The usual
       minimum arities still apply.
   * - Symbols and strings
     - Quoted and simple spellings identify the same symbol. Reserved
       words used as names require quoting, except that the SMT-LIB 2.6
       identifier ``lambda`` remains accepted. Strings escape a double
       quote by doubling it; backslashes are literal characters.
   * - Attributes and metadata
     - General attribute values and nested s-expressions are parsed.
       Unknown term attributes and metadata may be ignored; unknown
       options report ``unsupported``. A ``:named`` term must be closed
       and introduces a definition in the current declaration scope.
   * - Model inspection
     - ``get-model``, scalar and array ``get-value``, and ``get-assignment``
       for named Boolean terms. Abstract values of uninterpreted sorts
       are qualified, for example ``(as @S!0 S)``, and can be used in
       ``get-value`` for the same model.
   * - Other queries
     - ``check-sat-assuming`` accepts Boolean terms; ``get-unsat-assumptions``
       and ``get-unsat-core`` require their production options. Named cores
       report labels on active assertions. STP always retains assertions, so
       ``get-assertions`` works regardless of ``:produce-assertions``.
       ``get-info :all-statistics`` is available before solving and after
       context changes. Other information and option queries report the
       implemented settings.
   * - Random seed
     - ``:random-seed`` accepts unsigned 64-bit numerals and is used by
       every SAT backend. ``get-option`` reports the selected seed.
   * - Responses and channels
     - ``:print-success`` defaults to false. ``echo`` produces one string
       response. Regular and diagnostic output channels support
       ``stdout``, ``stderr`` and append-mode files. Errors produce an
       ``(error "...")`` response and end the script, consistent with
       ``:error-behavior immediate-exit``.

Compatibility with other frontends
----------------------------------

STP accepts common, unambiguous extensions rather than using the SMT-LIB
command modes as a strict input validator. The following cases were run
against cvc5 ``1.3.5.dev+main@1689f13331`` and Bitwuzla
``0.9.1-dev-main@f0f74238``. The table describes their default frontends;
cvc5's strict parser was also checked and differs here only by requiring
an explicit logic. These comparisons inform compatibility choices; the
2.7 reference remains the language target. In particular, that cvc5 build
reports that it uses 2.6 semantics when asked for version 2.7.

.. list-table::
   :header-rows: 1
   :widths: 40 20 20 20

   * - Input
     - cvc5
     - Bitwuzla
     - STP
   * - ``:produce-models`` after ``set-logic``, before declarations
     - Accepts
     - Accepts
     - Accepts
   * - No ``set-logic``
     - Accepts
     - Accepts
     - Selects ``ALL``
   * - Statistics before solving
     - Accepts
     - Command unsupported
     - Accepts
   * - ``get-assertions`` with ``:produce-assertions false``
     - Accepts
     - Command unsupported
     - Accepts
   * - Model query after ``define-fun``
     - Accepts
     - Accepts
     - Preserves the model
   * - Model query after ``push 0`` or ``pop 0``
     - Accepts
     - Rejects
     - Preserves the model
   * - A local ``let`` variable named ``and``
     - Accepts
     - Accepts
     - Accepts
   * - ``lambda`` as an ordinary identifier
     - Accepts
     - Accepts
     - Accepts; quotes it in output
   * - ``get-value`` after adding a contradictory assertion
     - Returns the prior model's value
     - Rejects
     - Rejects
   * - Model query without model production enabled
     - Rejects
     - Rejects
     - Rejects

Restrictions needed for a reliable answer remain. Assertions, declarations
and nonzero stack changes invalidate the current model. The existing
restriction on changing ``:global-declarations`` after declarations or
assertions prevents changing their scope retroactively. ``:reason-unknown``
requires an unknown result, as it does in cvc5; Bitwuzla does not implement
``get-info``.

Malformed option values, incorrect result sorts, malformed ``let`` bindings,
and non-closed ``:named`` terms still produce errors. The two other solvers
also reject the first three; cvc5 rejects non-closed named terms. Names
beginning with ``@`` or ``.`` remain reserved because STP uses them for
internal symbols and abstract model values. Local shadowing and the legacy
``lambda`` identifier are extensions; portable 2.7 scripts avoid shadowing
theory names and quote ``|lambda|``.

Random seed
-----------

``(set-option :random-seed 42)`` seeds the SAT backend through the same
setting as ``--random-seed=42``. The default, ``0``, leaves the backend's
own default in place. Nonzero seeds make its random choices repeatable
for the same input, backend and configuration. Different backends may
map the 64-bit seed into smaller ranges; distinct seeds need not produce
distinct results. Parallel solving and wall-clock limits can still make
runs differ.

For portable scripts, set the seed before ``set-logic``. STP also accepts
it after ``set-logic`` and between checks. A change preserves the last
model or core and rebuilds persistent solving state at the next solve.
``push``, ``pop`` and ``reset-assertions`` preserve the option; ``reset``
restores the startup value, including a seed supplied on the command line.
An API script's seed applies within that parse call; afterwards the
caller's solver options are restored.

Named unsat cores
-----------------

Enable ``:produce-unsat-cores`` before the check whose core is needed. Like
the other production options, it is accepted before or after ``set-logic``.
After an ``unsat`` answer, ``get-unsat-core`` returns a list of assertion
labels::

    (set-option :produce-unsat-cores true)
    (set-logic QF_BV)
    (declare-const p Bool)
    (declare-const q Bool)
    (assert (! p :named positive))
    (assert (! q :named unrelated))
    (assert (! (not p) :named negative))
    (check-sat)
    (get-unsat-core)
    ; unsat
    ; (|positive| |negative|)

STP projects its failed-assumption core onto named assertion occurrences.
Only an annotation on the whole asserted term contributes a label; naming
a nested subterm or using a previously defined name does not label an
assertion. Unnamed assertions remain background constraints. An empty
core is therefore possible when that background is already unsatisfiable.
Origins are retained through assertion-local lowering and conjunction
splitting. Repeated formulas and shared conjuncts can be represented by one
sufficient originating assertion; their other labels need not appear.

After ``check-sat-assuming``, assumptions also remain background for
``get-unsat-core``. When ``get-unsat-assumptions`` is enabled too, both
answers project the same engine core: the returned named assertions,
unnamed assertions and returned assumptions together are unsatisfiable.
Neither query prints the other query's entries.

Labels follow their assertions through ``push``, ``pop`` and
``reset-assertions``, even when ``:global-declarations true`` retains the
definitions introduced by ``:named``. A new check replaces the previous
core, and a context change makes it unavailable until another unsat check.

Cores need not be minimal. Core production engages the assumption solver
from the first check where supported. UF applications and whole-array
equality retain individual assertion origins through private SAT selectors,
including when solving requires theory refinement. This path bypasses UF
pre-propagation, whole-stack elimination and DISTINCT symmetry breaking:
those passes do not yet preserve dependencies for individual core entries.

With ``--incremental=off``, Real arithmetic, or a standalone DISTINCT-ordering
block without UF applications or whole-array equality, the engine still
exposes only a coarse core. Those checks return all active assertion labels
and, when requested, all user assumptions.

Remaining limits and extensions
-------------------------------

* Global sort parameters and polymorphic function declarations from 2.7
  are not implemented. ``declare-sort-parameter`` reports ``unsupported``.
  Parameterized sort aliases are supported, but ``declare-sort`` with a
  positive arity is not.
* Quantifiers, higher-order maps and ``lambda`` terms, datatypes,
  pattern matching and recursive definitions are not implemented.
  Datatype and recursive-definition commands report ``unsupported``;
  unsupported term syntax is rejected. A declaration that reported
  ``unsupported`` has not introduced a usable symbol.
* ``Int``, integer/bit-vector conversions, nonlinear real arithmetic,
  strings, sequences, sets and other theories outside STP's supported
  fragments are not implemented. Selecting ``ALL`` does not enable them.
* Arrays support Boolean, bit-vector, floating-point, rounding-mode and
  uninterpreted index and element sorts. Boolean indices have exactly two
  values, ``false`` and ``true``, and Boolean cells retain their ``Bool``
  sort in terms and models. Real and nested array components are not
  supported. Arrays are not accepted as uninterpreted
  function arguments or results.
* Proofs are not produced. ``:produce-proofs`` reports ``unsupported``
  when enabled; a query without an enabled
  production option is an error. Unsupported optional settings such as
  ``:reproducible-resource-limit`` also report ``unsupported``.
* Constant arrays, spelled ``((as const (Array I E)) value)``, are an
  extension used in array model output. ``fp.to_ieee_bv`` and some logic
  combinations are also extensions. Model text containing these forms
  needs a reader that supports them.
* Some older permissive syntax remains accepted, including extra
  parentheses in term positions. ``get-value`` echoes each queried term as
  the script spelled it, with runs of whitespace inside the term reduced to
  one space and comments removed. STP is not a strict syntax validator for
  arbitrary SMT-LIB input.

Unsupported commands and options have a response distinct from an error:
``unsupported`` leaves the script running. A malformed command, an invalid
command state, an unsupported logic or a rejected term ends the script.
These responses should be handled before using later results.

Regression coverage
-------------------

Language and protocol regressions live in
``tests/query-files/smt2-command-tests``, the theory-specific query files,
``tests/smtlib_protocol.py`` and the C++ parsing and model tests.
The protocol tests check output channels and exit status as well as
responses; model tests also replay values in fresh solver contexts.
See :doc:`testing` for running the suites. The coverage is a collection
of regression checks, not a certification of full SMT-LIB conformance.
