# libstp2: the 2.x C API implemented over the 3.x C API

`lib/Compat2` builds `libstp2`, a shared library that exports every one of the
236 functions of `include/stp/c_interface.h` (STP's 2.x C API) and implements
each of them over `include/stp/stp.h` (the 3.x C API) alone. It includes no
engine header and no `stp.hpp`; the one symbol it names beyond `stp.h` is the
workaround in defect 1 below. This file records how each 2.x behaviour is
reproduced, what is approximate or unsupported, how the 2.x acceptance suites
fare against it, and every 3.x defect met on the way.

## Files

| file | contents |
|---|---|
| `Compat2.h` | the internals shared by the two translation units: `Handle` (an `Expr`/`Type`), `VCImpl` (a `VC`), the UF declaration record, the helper declarations |
| `c_interface2.cpp` | process state (handler, policy, registries), handles and ownership, sort helpers, the option letters and ordinals, counters and schema groups, lifecycle, backends, assertions and queries, models and their printers, the presentation-language and SMT-LIB 2 printers, parsing, uninterpreted functions, introspection, `vc_simplify` |
| `c_interface2_terms.cpp` | every term and type constructor: types, symbols, Boolean, arrays, bit-vector constants and operations, floating point, Real |
| `CMakeLists.txt` | the `stp2` target, versioned like `stp`, installed beside it, exported with it |

## 1. Build and packaging

- `libstp2` is the only provider of the 2.x C API: `libstp` carries the 3.x
  API alone (with the engine's C++ interface, `cppinterface`, which the
  parsers and the 3.x API use). The 2.x headers, `c_interface.h` and the
  header-only `fp.hpp` and `uf.hpp` over it, are installed with `stp2`.
- The in-tree 2.x clients link `stp2`: the libstp2 test suites
  (`tests/api/compat2`), the two C tests of Real arithmetic
  (`tests/lra/real_c_api_smoke.c`, `real_c_api_undeleted_expr.c`), the
  install-test consumers of `c_interface.h` and `uf.hpp`, `tools/extdiff`
  (deliberately 2.x: the same source builds against the pre-feature baseline)
  and `tools/c_handle_churn_benchmark`. The 2.x ctypes Python package is gone;
  the `stp` Python package is the 3.x one.
- `STPConfig.cmake` sets `STP_C_INTERFACE_LIBRARY` to `stp2`, and names `stp2`
  in the older `STP_SHARED_LIBRARY` and `STP_STATIC_LIBRARY` too, since whoever
  reads those is a 2.x client; `export(TARGETS stp stp2 ...)` writes both
  targets into `STPTargets.cmake`. `stp2` is installed into
  `${CMAKE_INSTALL_LIBDIR}` with `INSTALL_RPATH "$ORIGIN"`, so an installed
  tree finds `libstp` next to it wherever it is moved. On Windows the output
  name is `stp2win`, mirroring `stpwin`.
- `include/stp/c_interface.h` gained one addition, the only header change:
  `enum stp_error_policy_t { STP_ON_ERROR_ABORT, STP_ON_ERROR_RETURN }` and
  `vc_setErrorPolicy()`, both honoured.

## 2. Shape

- **A `VC` is a `VCImpl`**: one `stp_tm`, one `stp_options` record, one
  `stp_solver` created lazily (see "option timing" below), a copy of the
  assertion stack (`levels`), the 2.x ownership state (`persist`, `exprdelete`,
  `tracking`), the UF declaration table, the cached `stp_model`, the last
  query, the reason-unknown record, the flags that change the shim's own
  behaviour (`'x'`, `'u'`, `'m'`, `'n'`, `'p'`, and whether a diagnostic print
  flag installed a sink) and the name of the SAT backend in use.
- **An `Expr` or `Type` is a `Handle`**, a small heap object holding one
  retained `stp_term` (or, for a `Type`, an `stp_sort`), the owning `VCImpl`,
  the ownership bit and a cached name. The term is deliberately the first
  member: a 3.x `stp_term` is the engine's `ASTInternal*`, and a 2.x
  `stp::ASTNode` is exactly one such pointer, so a test that reads
  `*(stp::ASTNode*)expr` (`GetKind()`, `BVTypeCheck`) sees the right node. That
  pun is what lets `fp-repeated-solve`, `fp-shared-bv-operand`,
  `fp-identity-passthrough` and three `array-extensionality` cases pass; it
  cannot help a test that casts the `VC` to `stp::STP*`.
- **`UFDeclHandle`s** are process-unique 64-bit ids (never reused) in a global
  `id -> owning VC` table, so a handle of a destroyed or foreign checker is
  refused without being dereferenced; the per-`VC` record holds the 3.x
  function term, the domain and codomain sorts and the name.
- **A `WholeCounterExample`** is a detached 3.x model snapshot (`stp_model`)
  plus its `VC`; `vc_getTermFromCounterExample` reads it with
  `stp_model_try_value`, which is what "the whole counterexample has no entry
  for this term" meant in 2.x.
- **Process state**: the error handler and the error policy (both global, as
  2.x's handler was), the set of live `VC`s (so a stale `VC` is refused rather
  than dereferenced), the `'u'` handle registry, the UF owner table; one mutex
  guards them.
- **Option timing.** 3.x fixes some options at solver construction
  (`sat-backend`, `lra-verify-canonical`) and many others before the first
  check (`incremental`, `array-equality`, `uninterpreted-functions`,
  `ackermanize`, the abstraction knobs, ...), refusing a late write with
  `OPTION_TIMING`. 2.x setters were write-only and took effect at the next
  query. The shim therefore records every setting in its `stp_options` and
  creates the solver only when something needs it; when a live solver refuses a
  write with `OPTION_TIMING`, the shim deletes it and creates a new one from
  the record, replaying the assertion stack (`push`es and `assert`s) into it.
  A nonfatal diagnostic would be the simpler answer, but the acceptance
  suites switch backends and flags between queries and expect them to take
  effect, which the rebuild gives them. Refusals for
  any other reason are reported through the handler and the setting is dropped.
- **Errors.** `report()` is the nonfatal path: the handler if one is
  registered, else `CInterface: <message>` on stderr; the call returns its
  failure value. `fatal()` calls the handler, prints `Fatal Error: <message>`
  and aborts, unless `vc_setErrorPolicy(STP_ON_ERROR_RETURN)` is in force, in
  which case the call returns `NULL`/0/2 instead and the checker stays usable.
  The fatal texts reproduce 2.x's where the 2.x death tests match on them
  ("requires bitvector operands", "requires operands of the same sort",
  "expected a rounding mode", "expects a type node", "cannot be redeclared",
  "at least 2 exponent and 2 significand bits", "number of bits in an array's
  elements must be a positive integer", "stored value sort differs from the
  array's bitvector element sort", the array-equality refusal, and so on).
- **Threads.** Each `VC` is its own 3.x manager, which 3.x pins to the creating
  thread, as 2.x did in effect. `vc_createValidityChecker` boots the constant
  bit-vector library on the calling thread once per thread (defect 1).

## 3. Mapping decisions

1. **Results.** `vc_query`/`vc_query_with_timeout` map `stp_solver_entails`:
   VALID -> 1, INVALID -> 0 (and the model is cached), UNKNOWN -> 3, any
   failure -> 2 after the diagnostic. Negative budgets other than -1 return 2
   with a message on stderr, as 2.x did. A query prints `Valid.`/`Invalid.`/
   `Unknown.` under `'n'` and the counterexample under `'p'`.
2. **Reason unknown.** The 3.x reason is mapped to the 2.x enum
   (RESOURCE_LIMIT -> AIG_BUDGET, CONFLICT_LIMIT -> CONFLICT_BUDGET, TIMEOUT,
   CARRIER_EXHAUSTED, ASSUMED_INJECTIVITY, everything else -> INCOMPLETE) and
   `stp_solver_last_reason_message` is the text `vc_getReasonUnknownToBuffer`
   returns. Both are cleared at every query (2.x's defect D1 is not
   reproduced).
3. **Ownership.** Term and type constructors return checker-owned handles:
   with `EXPRDELETE` at its default (1) they are recorded in the checker's
   persist list and freed by `vc_Destroy`, and `vc_DeleteExpr` may free one
   early; with `EXPRDELETE = 0` they are not recorded, and the caller frees or
   leaks them, the 2.x profile KLEE relies on. Readers return caller-owned
   handles that `vc_DeleteExpr` frees: `vc_getCounterExample`,
   `vc_getCounterExampleArray`, `vc_getTermFromCounterExample`,
   `vc_getUninterpretedFunctionValue`, `vc_applyUninterpretedFunction`,
   `vc_parseExpr`/`vc_parseMemExpr`, `getChild`, `vc_simplify`. A handle is
   never aliased: the zero shift and the no-op extend return fresh handles.
4. **The `'u'` registry.** Once `'u'` is set, every handle the checker creates
   is registered (and the checker-owned ones that predate the flag are
   adopted), so the UF entry points can validate an `Expr` argument through the
   registry without dereferencing it; `vc_DeleteExpr` unregisters. The
   registry costs nothing until `'u'` is used anywhere in the process.
5. **Model lifetime.** The model is a 3.x snapshot taken when a query answers
   INVALID. As in 2.x it survives `vc_pop` and `vc_assertFormula` and is
   discarded on `vc_push` and at every query; a read with none behind it
   returns `NULL` after the diagnostic "no model to read -- no query has been
   answered since the last vc_push or vc_query". A constant is its own value
   and needs no model. A read after a VALID answer is a read with no model
   (2.x's D2 invented `0`/`false`; not reproduced). The UF rule is the strict
   2.x one: `vc_getUninterpretedFunctionValue` (and `vc_getCounterExample` on
   an application) answers only from the model of the last satisfiable query
   with no assertion, push or pop since ("certified"), and only for an
   application whose argument tuple that solve observed; an argument over a
   symbol outside the model's core (`stp_model_try_value` is `NULL` for it) is
   "not reachable from the last satisfiable query" and gets `NULL` plus the
   diagnostic.
6. **Array cells.** `model-array-fill` is `ones` for every checker (2.x
   completed an unobserved cell to `0xFF`) and `zero` once `'x'` is set (2.x
   completed to `0x00` with it).
7. **Letters** (`vc_setFlag`, `vc_setFlags`, `process_argument`): `'a'`
   disable-opt-inc, `'c'` produce-models, `'d'` produce-models + check-sanity
   (on for every checker, as 2.x forced it), `'i'` incremental=on, `'r'`
   ackermanize, `'u'` uninterpreted-functions=on + the registry, `'w'`
   switch-word, `'x'` array-equality=on + model-array-fill=zero, `'m'`
   (SMT-LIB 1 input for the parse functions), `'n'` (print the answer), `'p'`
   (print the counterexample) are shim-side switches, `'q'`, `'s'`, `'t'`,
   `'v'`, `'y'` set the corresponding print options and install a stdout
   diagnostic sink on the solver, `'h'` is fatal (nothing a library can act
   on), and any other letter is fatal as in 2.x. `vc_setFlags`'s
   `num_absrefine` is ignored, as 2.x ignored it.
8. **Ordinals** (`vc_setInterfaceFlags`): every one of the 70 values of
   `ifaceflag_t` is handled. `EXPRDELETE` is the ownership switch above;
   `MS`/`MSP` select minisat, `SMS` simplifying-minisat, `CMS4` cryptominisat,
   `CADICAL` cadical (a construction-time option: the solver is rebuilt, see
   §2); the unsigned knobs refuse a negative value with "<FLAG> must not be
   negative" and leave the setting alone; `UF_ACKERMANN` 0/1/2 -> auto/on/off;
   `CNF_GENERATION_EFFORT` 0..12 -> the 3.x names very-low, low, medium, high,
   very-high, auto, new-very-low, new-low, new-medium, gia-low, gia-high,
   gia-very-high, new-high; `BV_TERM_ABSTRACTION_PROFILE` 0/1/2 ->
   qualified/broad/aggressive; `BV_TERM_ABSTRACTION_MULT` also sets the divmod
   switch unless `BV_TERM_ABSTRACTION_DIVMOD` was named explicitly (the 2.x
   scope rule); `FP_ABSTRACTION_OPS`/`FP_ABSTRACTION_CHAIN_OPS` masks become
   the option's name lists ("default" and "none" for 0); the tri-states
   `UF_BV_TERM_ABSTRACTION` and `FP_ABSTRACTION_CONSTANT_OPERANDS` are
   0 off / 1 on / other auto; `AIG_NODE_BUDGET` takes -1 or a count;
   `INCREMENTAL_AUTO_ENGAGE_AT` restores the default for any negative value;
   the `LRA_*` and remaining Booleans are `true`/`false`. `UF_SORT_WIDTH` is
   validated (1..1024) and recorded only: in 3.x the width is a manager-scoped
   setting of an uninterpreted sort the 2.x API cannot declare, so nothing can
   observe it.
9. **Counters.** `vc_getCounter` reads a `stp_statistics` snapshot of the
   solver through a table from `stp_counter_t` to the 3.x statistic name
   (`checks.bitblasted`, `bv.candidates.*`, `bv.abstracted.*`,
   `bv.refinement_rounds`, `bv.blocking_lemmas`, `uf.*`, `bv.schema_lemmas`,
   `bv.exact.*`, `bv.schema.*`, `fp.*`); a name the snapshot lacks reads 0,
   and a checker without a solver yet reads 0. `vc_setSchemaGroups` writes
   `bv-term-abstraction-schema-groups`; `vc_schemaGroupName` and the
   out-of-range refusal come from a 15-name table. `vc_getSchemaGroupCounter`
   reads `bv.schema_group.<name>.lemmas`.
10. **Backends.** `vc_supports*` is `stp_has_sat_backend`; `vc_use*` sets
    `sat-backend` and rebuilds the solver; `vc_isUsing*` compares the recorded
    name, which starts as the first available of cryptominisat, cadical,
    minisat (the engine's own resolution of "auto").
11. **Presentation-language printers.** Terms are printed with
    `stp_term_to_string(STP_FORMAT_CVC)`; the shim composes the surrounding
    forms 2.x produced: `ASSERT( <term> );` for `vc_printAsserts`,
    `QUERY(<term>);`, the `x : BITVECTOR(n);` / `ARRAY BITVECTOR(i) OF
    BITVECTOR(e)` / `BOOLEAN` declarations of `vc_printVarDecls` from
    `stp_tm_symbols` (with a `vc_clearDecls` watermark; symbols of sorts the
    language cannot spell are skipped), and the
    `COUNTEREXAMPLE BEGIN: ... COUNTEREXAMPLE END:` block with `ASSERT( x =
    0xFF );`, `ASSERT( a[i] = v );` and `<=>` lines for the model. Printing a
    floating-point or Real term in the presentation language is the 2.x fatal
    "the presentation language has no floating-point syntax; print this with
    SMTLIB2_PrintBack (vc_printSMTLIB2 in the C API)"; `exprString` falls back
    to the SMT-LIB 2 spelling for such a term instead of dying (2.x died inside
    the printer). `vc_printExprFile`/`vc_printCounterExampleFile` write to the
    descriptor with `write(2)`.
12. **SMT-LIB 2 printers.** `vc_printSMTLIB2(e)` and
    `vc_printCounterExampleSMTLIB2` are composed by the shim, not by
    `stp_solver_to_smt2`/`stp_model_to_smt2`: the 2.x form is `(set-logic ...)`
    chosen from the symbols in `e` (QF_BV, QF_ABV, QF_UFBV, QF_AUFBV, QF_BVFP,
    QF_ABVFP, QF_UFBVFP, QF_AUFBVFP, QF_AX, QF_LRA, QF_UFLRA),
    `(set-info :smt-lib-version 2.0)`, `(declare-fun |x| () sort)` per symbol,
    `(assert e)`, and `(define-fun |x| () sort value)` per model entry (arrays
    through `stp_array_value_as_term`, functions from the entries of
    `stp_fun_value`), and the 3.x printers spell names unquoted with a double
    space after an operator (recorded in `lib/Api/c/NOTES.md`).
13. **Hash.** `vc_getHashQueryStateToBuffer` is `stp_term_hash` of the
    conjunction of the negated query with every assertion on the stack (the
    design suggested a text hash; a hash value was never stable across
    versions, and the term hash is the one the engine already maintains).
14. **Parsing.** 3.x's CVC parser asserts the *negation* of a `QUERY`
    (`stp_solver_parse` semantics). To give 2.x's `vc_parseExpr`/
    `vc_parseMemExpr` their `asserts` and `query` back, the shim splits the
    text: the script is parsed with its `QUERY` statement replaced by
    `QUERY TRUE;`, then `QUERY <f>;` alone is parsed inside a push/pop and the
    assertion it added is negated back into the query term. With `'m'` the
    text is SMT-LIB 1: everything is asserted and the query is `FALSE`, as the
    2.x parser had done. `vc_parseExpr` returns the conjunction of the asserts
    with the negated query, as 2.x did; a file that cannot be opened is the 2.x
    fatal "Cannot open file", a parse failure is fatal with the 3.x message.
15. **Kinds and children.** `getExprKind` maps every public 3.x kind to the
    nearest `exprkind_t` (a VALUE reports TRUE/FALSE/BVCONST/REAL_CONST, a
    float or rounding-mode constant reports BVCONST as 2.x did, a Boolean
    `stp_eq` reports IFF and a float one FP_SMT_EQ, APPLY is UF_APPLY,
    SELECT/STORE are READ/WRITE, the `to_fp` family folds onto
    FP_TOFP/FP_TOFP_SIGNED/FP_TOFP_UNSIGNED); kinds 2.x could not spell
    (repeat, rotate, bvcomp, the signed-overflow predicates 2.x lacked, redand/
    redor, constant arrays, fp.to_real) report UNDEFINED. `getDegree`/
    `getChild` give the public children. Because the checker uses the
    simplifying factory, the kind reported is the *simplified* term's
    (`stp_term_get_kind` is guaranteed under `simplify = false` only): a
    zero-extend comes back as BVCONCAT, `bvnand` as BVNOT, `x <= y` over floats
    as FP_GEQ, a Boolean equality as NOT, exactly the shapes 2.x's internal
    view showed. Nothing in the acceptance suites walks a tree through this
    interface.
16. **Uninterpreted functions.** `vc_declareUninterpretedFunction` needs `'u'`,
    a positive arity, live tracked `Type` handles over Bool/BV/FP/RM/Real and a
    name that is neither an ordinary symbol nor a declared function; it is
    `stp_mk_fun_sort` + `stp_declare`. `vc_applyUninterpretedFunction` checks
    the owner, the arity, that every argument is a live tracked handle of the
    declared sort, and is `stp_apply_n`. `vc_getUninterpretedFunctionValue`
    is the certified read of decision 5.
17. **Floating point.** `vc_fpRoundingMode` takes the one-hot `VCRoundingMode`
    (RNE=1, RTP=2, RTN=4, RTZ=8, RNA=16); a float or rounding-mode model value
    is read as its packed bits by `getBVUnsignedLongLong` and friends (2.x
    exposed them that way); `vc_fpConstFromDouble`/`FromFloat` go through the
    native bits; the four `vc_fpToFP*` forms and the two `vc_fpToBV*` forms are
    the 3.x conversions; `vc_fpRemExpr` reports 3.x's UNSUPPORTED refusal for
    a format its circuit cannot unroll with the 2.x wording. Every FP
    constructor is checker-owned. `include/stp/fp.hpp` is header-only over
    these functions and works unchanged (`fp-cpp-wrapper` passes).
18. **Real.** All 21 `vc_real*`/`vc_getRealModel*`/`vc_hasReal*` functions are
    the 3.x Real constructors and readers; a `RESOURCE` refusal of a literal is
    a nonfatal `NULL`, any other refusal is fatal, as 2.x had it. An assertion
    the engine refuses (`UNSUPPORTED` from `stp_solver_assert`: the
    exact-arithmetic budget, at preregistration) is reported through the
    handler and left out, and, as in 2.x, every query at that depth or deeper
    answers 3 with `REASON_UNKNOWN_INCOMPLETE` until a `vc_pop` leaves the
    depth (`reason-unknown` tests it).
19. **Array equality.** `vc_eqExpr` over two arrays without `'x'` is the 2.x
    fatal "STP cannot decide equality between whole array terms without
    --array-equality ...", raised at construction (3.x would build the term
    and decide it whenever `array-equality` is on); with `'x'` it is `stp_eq`,
    an extensional equality.
20. **Symbol names** are unrestricted (2.x made `@`/`.` prefixes fatal); the
    3.x manager keys symbols by name and sort, so re-declaring a name at
    another sort is the 2.x fatal "cannot be redeclared".
21. **`vc_Destroy`** frees the persist list and every tracked handle of the
    checker, the whole counterexamples it handed out, the cached model, the UF
    function terms, the last query, the stack copy, the solver and the options,
    then `stp_tm_release_all` and `stp_tm_release`.

## 4. Approximate and unsupported functions

| function | status |
|---|---|
| `vc_createValidityCheckerReuse` | **unsupported**: returns `NULL` after a diagnostic through the handler. 3.x has no door through which a raw engine manager can be adopted. Calling any function on the `NULL` result is then the usual fatal. |
| `vc_setInterfaceFlags(UF_SORT_WIDTH)` | **inert**: validated and recorded, nothing observes it (decision 8). |
| `vc_setFlags(..., num_absrefine)` | the second argument is ignored, as in 2.x. |
| `vc_setFlag('h')` | fatal ("help" is not a flag a library can act on); 2.x printed the help and exited. |
| `getExprKind`, `getDegree`, `getChild` | **approximate**: public kinds and children of the simplified term (decision 15). |
| `vc_getHashQueryStateToBuffer` | a different hash function than 2.x's (decision 13); values were never stable across versions. |
| `exprString` on a float/Real term | the SMT-LIB 2 spelling instead of 2.x's death inside the printer. |
| `vc_printVarDecls` | symbols of float, rounding-mode and Real sorts are skipped (the presentation language cannot spell them; 2.x printed nothing usable for them either). |
| `vc_getCounterExample` after a VALID answer | `NULL` plus a diagnostic instead of 2.x's invented value (D2, deliberate). |
| `vc_pop` at the base level | fatal instead of 2.x's deletion of the base assertions (D10, deliberate). |
| `vc_parseExpr` / `vc_parseMemExpr` | reproduced by the split described in decision 14; a script with several `QUERY` statements keeps only the last, as 2.x did. |
| `vc_printSMTLIB2`, `vc_printCounterExampleSMTLIB2`, `vc_getRealModelSMTLIB2` | composed by the shim (decision 12); the text is the 2.x form, not the 3.x printers' form. |
| `vc_setErrorPolicy` | new, honoured; under `STP_ON_ERROR_RETURN` every fatal path returns its failure value after the handler. |

Everything else is a direct mapping.

## 5. Test results

What follows is the qualification of `libstp2` against the whole 2.x test
suite, run on 2026-09-27 before those suites were rewritten against the 3.x
API (they are now in `tests/api/cpp3`); it is the record of what `libstp2`
reproduces and why the rest cannot be. At the time the 2.x implementation
could still be compiled into `libstp`, which the control runs below used; the
option that chose between the two, `STP_LEGACY_C_INTERFACE`, is gone, and
"option OFF" below is today's only configuration. The suites that still run
against `libstp2` are listed at the end of this section.

Configuration: `-DSTP_LEGACY_C_INTERFACE=OFF -DENABLE_TESTING=ON
-DTEST_CPP3_API=OFF -DUSE_CADICAL=ON` (CryptoMiniSat available, MiniSat off),
RelWithDebInfo, in `build-stp2`; the control tree `build-stp2-on` is the same
with the option `ON`. No test source was edited. One test *fixture* was:
`tests/api/install/uf-public-header-consumer/CMakeLists.txt` links
`${STP_C_INTERFACE_LIBRARY}` (from `STPConfig.cmake`) instead of `stp`, so the
installed-package check links the library that actually provides the API.

### ctest, `tests/api/C`, option ON (the 2.x implementation, control)

```
100% tests passed, 0 tests failed out of 79
```

`tests/api/python`: `python-interface-tests` and `python-allocator-tests`
passed (2/2).

### ctest, `tests/api/C`, option OFF (libstp2)

```
84% tests passed, 13 tests failed out of 79
```

The 13 failing *binaries* are `fp-abstraction-flags`, `cnf-effort-flag`,
`incremental-scoped-preprocessing`, `array-extensionality`,
`incremental-auto-engage`, `push-pop-model`, `refinement-flags`, `simplify`,
`fp-repeated-solve`, `uninterpreted-functions-handle-safety`,
`fp-model-roundtrip`, `fp-multi-checker`, `model-read-with-no-solve`.
(`fp-model-roundtrip` passes since the partial floating-point choice was fixed
in the 3.x model, D below: 12 binaries and 318 of 366 cases as of 2026-09-27.)

### ctest, `tests/lra`, option OFF (libstp2), 2026-09-27

The 89 LRA tests run against libstp2 as well. Four fidelity gaps their C-API
acceptance tests exposed were closed the same day: a null or foreign operand
is refused with 2.x's wording ("received a null Expr", "received an Expr owned
by a different validity checker") before any sort check, an `ite` whose
branches disagree on Real is refused as "requires Real operands", the width
getters (`getVWidth`, `getIWidth`, `vc_getExpWidth`, `vc_getSigWidth`) report
the engine's fatal messages on a Real instead of answering 0, and
`vc_printSMTLIB2` prints the body with the engine printer (`|quoted|`
symbols, Reals as numerals) rather than the 3.x unshared printer. 2.x's rule
that the exact Real model is current only until the checker changes (a
declaration of any sort, an assertion, a push or a pop each invalidate it
until the next INVALID query republishes it) is reproduced by
`real_model_current`; the bit-vector counterexample keeps its own longer life.
`lra_c_api_smoke` and `lra_c_api_negative` pass. `lra_real_capability_api`
fails one case, `real-uf-scalar-model-completion` ("no exact Real model was
published"): the model value of a Real-valued uninterpreted-function
application is a 3.x alpha gap (no model table for Real-valued applications,
`lib/Api/README.md`), so the checker has nothing to publish for it.

Per-case tally of every `tests/api/C` binary on the same day, each case in
its own process: 401 of 445 cases pass; the 44 that do not are the classes
below (array-extensionality 15, refinement-flags 13, cnf-effort-flag 4,
incremental-auto-engage 3, fp-abstraction-flags 2, push-pop-model 2, and one
each of incremental-scoped-preprocessing, fp-multi-checker,
model-read-with-no-solve, simplify, uninterpreted-functions-handle-safety).
`tests/api/python`: `python-interface-tests` (83 cases) and
`python-allocator-tests` passed (2/2), loading `libstp2.so`.

Running every gtest case of every binary in its own process (a crashing case
takes its whole binary down under ctest): **317 of 366 cases pass**. The 49
that do not, with the reason:

**A. The test reaches engine internals through the `VC` handle (45 cases).**
These cast the `VC` to `stp::STP*` and read or write `->bm->UserFlags`,
`->bm->getExtensionalityIfAny()`, `->bm->getUFContext()`,
`->hasIncrementalSolver()`, or build engine nodes on `->bm`. A `VC` from
libstp2 is a `VCImpl`, so the reads are garbage and the writes crash. No shim
over the public API can pass them; the property each one checks is not one the
C API exposes.

- `array-extensionality` (16 of 31; the other 15 pass):
  `active_checker_owns_complete_array_graph`,
  `active_equalities_follow_assertions_and_query`,
  `asserted_ite_condition_folds_before_fe03`, `equality_under_push_pops_away`,
  `flag_on_without_equalities_is_dormant`,
  `ite_replacement_survives_a_rewritten_condition`,
  `lemma_atoms_fold_at_encoding`, `nested_ite_fixed_point_is_stable`,
  `refinement_on_the_cadical_backend`,
  `repeated_queries_do_not_leak_ite_records`,
  `store_chain_equals_base_solved_by_rewrite`,
  `store_chain_guarded_inner_write`, `store_chain_over_write_base`,
  `store_chain_shadowed_write_is_unconstrained`,
  `store_index_read_through_second_array_unsat`,
  `unlinked_reads_are_owned_by_the_extensionality_checker` (SIGSEGV at
  `static_cast<stp::STP*>(vc)->bm->UserFlags...` or the
  `ExtensionalityContext` reads).
- `refinement-flags` (14 of 16): every case that calls the file's
  `flags(vc)`/`mutableFlags(vc)` (`((stp::STP*)vc)->bm->UserFlags`):
  `DefaultsAreTheOnesTheCommandLineDocuments`,
  `EachFlagReachesTheFieldTheCLIWrites`,
  `TheDivModScopeResolvesTheSameWayInEitherOrder`,
  `AProfileDoesNotOverwriteACeilingTheCallerNamed`,
  `AProfileDoesNotOverwriteAGroupListTheCallerNamed`,
  `AnUnknownSchemaGroupNameIsRefused`, `InvalidBVProfileIsAtomic`,
  `EachSchemaGroupIndexReadsItsOwnCounterAndName`,
  `EverySchemaGroupNameRoundTripsThroughTheSelector`,
  `ExactCostCountersReachTheCInterface`,
  `ANegativeUnsignedValueIsRefusedAndLeavesTheFieldAlone`,
  `TheSortWidthIsRefusedOutsideTheRangeTheCLITakes`,
  `AnUnknownAckermannModeIsRefused`,
  `NarrowingChangesNeitherTheAnswerNorTheSortReadBack`. The two cases that
  stay on the C API (`AnOutOfRangeSchemaGroupIndexIsRefused`,
  `TheAigBudgetEndsAQueryWithoutAnAnswer`) pass.
- `cnf-effort-flag` (4 of 5): `TheDefaultIsAuto`,
  `TheAutoThresholdIsReachableThroughTheCAPI`, `EveryLevelIsReachable`,
  `OutOfRangeIsRefusedAndLeavesTheLevelAlone` read `flags(vc)`;
  `EveryLevelDecidesTheSameQuery` passes (every effort level is set through
  the shim and decides the query).
- `fp-abstraction-flags` (2 of 4): `EverySetterReachesItsOwnField`,
  `NegativesAreRefusedAndChangeNothing` read `flags(vc)`; the two counter
  cases pass.
- `incremental-scoped-preprocessing` (2 of 3): `ItIsOffByDefault`,
  `TheFlagReachesTheField`; `TheAnswersDoNotChange` passes.
- `incremental-auto-engage` (3 of 4): `DefaultKeepsTheFirstTwoQueriesOnBatch`,
  `ZeroNeverEngages`, `EarlyEngagementDoesNotChangeAnswersOrModels` fail on
  `engaged(vc)` = `((stp::STP*)vc)->hasIncrementalSolver()`, a garbage read
  (the answers and models they also check are right);
  `ThresholdOfOneEngagesOnTheFirstQuery` passes by the luck of that read.
- `push-pop-model.counterexample_survives_pop_until_next_query`: every model
  expectation passes; the single failing line is
  `EXPECT_FALSE(((stp::STP*)vc)->hasIncrementalSolver())`.
- `simplify.native_distinct_is_lowered_before_preprocessing`: builds a native
  `DISTINCT` node on `->bm` (the two other cases pass).
- `fp-repeated-solve.floating_point_activation_is_query_local`: writes
  `->bm->UserFlags.difficulty_reversion` (the other two pass through the
  `ASTNode` pun).
- `uninterpreted-functions-handle-safety.InvalidAndInactiveDeclarationHandlesAreNonfatal`:
  `->bm->getUFContext()->lookup/deactivate` (the other 10 pass).

**B. `vc_createValidityCheckerReuse` (2 cases).**
`fp_multi_checker.checker_reuse_over_existing_manager` and
`push_pop_model.file_printer_materializes_deferred_counterexample` construct an
`stp::STPMgr` and build a checker around it (the second also writes its
`UserFlags`). The shim returns `NULL` (see the function table), and the next call aborts on the
null checker.

**C. A documented 3.x semantic change (1 case).**
`model_read_with_no_solve.a_valid_query_is_not_the_same_as_no_query` expects
`vc_getCounterExample` to answer after a VALID query; that is 2.x's D2
(inventing a value where there is no model), not reproduced by design. The other 12 cases of the binary pass.

**D. A 3.x defect (1 case), FIXED.**
`fp_model_roundtrip.partial_choice_uses_current_solve_encoding` asserts
`fp.min(+0, -0) = +0`, gets INVALID, and reads the model value of the
`fp.min`: the 3.x model said `-0` (defect 2). The model snapshot now records
the solve's choice for every partial floating-point operation in the checked
formula, and the whole binary passes.

The facades: `fp-cpp-wrapper` (all cases over `include/stp/fp.hpp`) passes;
the two installed-header consumers of `include/stp/uf.hpp` and the C API
(`tests/api/install/uf-public-header-consumer/main.cpp`, `main.c`) were
compiled by hand against `libstp2` and exit 0.

Under the option `ON` nothing changed: 79/79 binaries and 2/2 Python suites,
as before this work.

### What runs against libstp2 now

- `tests/api/compat2`: eleven of the 2.x gtest suites, unchanged (the handle
  lifecycle, counterexamples, push and pop, parsing, `Expr` ownership, the
  counter enum's ABI, floating point and `fp.hpp`, uninterpreted functions,
  arrays, and the reason a query had no answer), each linked to `stp2`.
- `tests/lra`: `lra_c_api_smoke` and `lra_c_api_undeleted_expr`, the C tests of
  the Real extension.
- `tests/api/install`: the C and C++ (`uf.hpp`) consumers of an installed
  `c_interface.h`, linking `${STP_C_INTERFACE_LIBRARY}`.

## 6. 3.x defects met

1. **Two managers on two threads corrupt the heap.**
   *Files:* `lib/Api/Manager.cpp`, `boot_constant_bv()` (a process-wide
   `std::call_once` around `CONSTANTBV::BitVector_Boot()`), together with
   `lib/extlib-constbv/constantbv.cpp`, where every machine constant Boot sets
   (`BITS`, `LOGBITS`, `MODMASK`, `FACTOR`, `BITMASKTAB`, ...) is
   `THREAD_LOCAL_IE`. *Symptom:* the first manager created on any thread other
   than the first booting thread runs with zeroed constants; its first constant
   (`BitVector_Create(65, ...)` under `STPMgr::CreateBVConst`) computes a
   65-word size at a 68-byte allocation and zeroes 260 bytes: SIGSEGV inside
   the allocator, or glibc's `malloc.c: sysmalloc: assertion failed`. A
   reproducer with nothing but `stp.h` (two threads, each `stp_tm_new`,
   `stp_mk_fp_sort`, `stp_mk_rm`, a query, release) fails on every run;
   valgrind reports the invalid writes in `BitVector_Create` called from
   `stp_mk_rm`. `stp.h`'s thread contract ("independent managers are
   concurrent") is violated. *Fix in 3.x:* boot per thread (a `thread_local`
   flag in `boot_constant_bv`, or the boot inside `stp_tm_new` on the calling
   thread). *Workaround in the shim:* `vc_createValidityChecker` calls the
   library's C-linkage `BitVector_Boot()` once per thread (a `thread_local`
   flag), which is what 2.x's `vc_createValidityChecker` always did; the
   declaration is the one symbol libstp2 uses beyond `stp.h` and goes with the
   defect. Failing test before the workaround:
   `fp_multi_checker.concurrent_floating_point_queries`.
2. **The model of a partial floating-point operation contradicts the solve.**
   *File:* `lib/Api/Model.cpp`, the evaluator's handling of `FP_MIN`/`FP_MAX`
   (and `FP_TO_UBV`/`FP_TO_SBV`): it totalises the operation with a constant
   zero "choice" child before folding. *Symptom:* with `(= (fp.min +0 -0) +0)`
   asserted and the check `sat`, `stp_model_value` and `stp_model_try_value`
   of the `fp.min` term give `(fp #b1 #b00000 #b0000000000)`, i.e. `-0`, the
   opposite of what the solve chose and what the assertion requires. The
   choice the solve made is not reachable from the model, so the shim cannot
   repair the value. Failing test:
   `fp_model_roundtrip.partial_choice_uses_current_solve_encoding`.
3. **No per-schema-group statistics** (fixed). The 3.x snapshot had
   `bv.schema_lemmas` only, so `vc_getSchemaGroupCounter` answered 0 for
   every group; it now publishes `bv.schema_group.<name>.lemmas` per group,
   which the shim reads unchanged.
4. **`stp_model_try_value` completes an unobserved function application.**
   *File:* `lib/Api/Model.cpp` (evaluation of `APPLY`). The header promises
   `NULL` "if completion would be needed"; for `f(8)` where the solve never
   observed the tuple `(8)`, it returns the function's default value instead.
   The shim therefore cannot use `try_value` on the application to tell an
   observed tuple from a completed one and matches the argument values against
   `stp_fun_value`'s entries itself (decision 5).
5. **The 3.x SMT-LIB 2 printers' spelling** (`stp_solver_to_smt2`,
   `stp_model_to_smt2`, `stp_term_to_string(STP_FORMAT_SMTLIB2)` for a whole
   script): symbol names unquoted and a double space after an operator
   (`(bvadd  #x01 ...)`), already recorded in `lib/Api/c/NOTES.md`. Legal
   SMT-LIB, but not the text the 2.x tests compare against, which is why the
   shim composes its own (decision 12). The term printer itself does quote
   (`|x|`).
6. **`stp_term_get_kind` under the simplifying factory.** Documented in
   `stp.h` as "guaranteed under simplify = false only", so not a defect, but
   the reason `getExprKind` is approximate (decision 15): the checker cannot
   run with `simplify = false` (it is the mode 2.x ran in, and the results the
   suites expect depend on it).

## 7. Deliberate choices

- Option timing: a rebuild with stack replay, not a diagnostic (§2 above).
- `vc_getHashQueryStateToBuffer`: a term hash, not a text hash.
- `vc_printSMTLIB2` and the model's SMT-LIB 2 text: composed by the shim, not
  taken from a scratch solver's `to_smt2` (defect 5).
- The UF model rule stays the strict 2.x one (dies on assert, push and pop)
  rather than a permissive one: the UF suites test the strict rule.
- Whole-array equality without `'x'` is refused at construction, as in 2.x,
  although the 3.x API would build it.
- The per-thread boot of the constant bit-vector library (defect 1).

## 8. Follow-ups

- Remove the `BitVector_Boot` declaration and `boot_constant_bv_on_this_thread`
  once 3.x boots the library per thread.
- If the 3.x model carries the totalisation choice of a partial floating-point
  operation, `fp_model_roundtrip.partial_choice_uses_current_solve_encoding`
  passes with no change to the shim.
