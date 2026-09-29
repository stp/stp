SMT-LIB 2.7 compatibility
========================

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
-----------------------------------------

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
       ``:named`` inline definitions. Theory names cannot be shadowed in
       their own namespace. A qualification checks the result sort; it
       does not convert a value.
   * - Operator attributes
     - N-ary Core connectives and equality, including Real equality;
       pairwise ``distinct``; right-associative implication; supported
       bit-vector operators with their associative syntax. The usual
       minimum arities still apply.
   * - Symbols and strings
     - Quoted and simple spellings identify the same symbol. Reserved
       words used as names require quoting. Strings escape a double quote
       by doubling it; backslashes are literal characters.
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
       requires its production option. STP always retains assertions, so
       ``get-assertions`` works regardless of ``:produce-assertions``.
       ``get-info :all-statistics`` is available before solving and after
       context changes. Other information and option queries report the
       implemented settings.
   * - Responses and channels
     - ``:print-success`` defaults to false. ``echo`` produces one string
       response. Regular and diagnostic output channels support
       ``stdout``, ``stderr`` and append-mode files. Errors produce an
       ``(error "...")`` response and end the script, consistent with
       ``:error-behavior immediate-exit``.

Remaining limits and extensions
------------------------------

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
* Arrays currently require bit-vector, floating-point, rounding-mode or
  uninterpreted index and element sorts. Boolean, Real and nested array
  components are not supported. Arrays are not accepted as uninterpreted
  function arguments or results.
* Proofs and named unsat cores are not produced. Their production options
  report ``unsupported`` when enabled; a query without an enabled
  production option is an error. Unsupported optional settings such as
  ``:random-seed`` also report ``unsupported``.
* Constant arrays, spelled ``((as const (Array I E)) value)``, are an
  extension used in array model output. ``fp.to_ieee_bv`` and some logic
  combinations are also extensions. Model text containing these forms
  needs a reader that supports them.
* Some older permissive syntax remains accepted, including extra
  parentheses in term positions. ``get-value`` may print a normalized
  spelling of the queried term. STP is not a strict syntax validator for
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
