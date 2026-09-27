# The C layer: notes against the design sketch

`include/stp/stp.h` realises `api-3x/design/stp.h` (the sketch) over the
implemented C++ API. This file records where the two differ, the decisions
the sketch left open, and what the C++ side did not offer.

## Files

| file | contents |
|---|---|
| `stp_c_internal.h` | the runtime structures: `CManager` (per-manager state), the handle structs, `ErrorRecord`, the exception boundary `guarded`, the solver's `solver_mutate`/`solver_checked` |
| `stp_c.cpp` | managers, reference counts, scopes, the error record and callback, the library queries, sorts, symbols, values, generic and named construction (includes the generated `kind_ctors_c.inc`), term introspection and readers |
| `stp_c_options.cpp` | standalone `stp_options`, the registry introspection, the live options of a solver |
| `stp_c_solver.cpp` | solver, model, array/function values, statistics |

## How the runtime is built

- **A term handle is the engine node** (`ASTInternal*`), as the sketch requires.
  The manager behind a term-only call (`stp_term_str(t)`, `stp_term_release(t)`,
  ...) is found through the node's `STPMgr*` (`ASTNode::GetNodeManager()`) in a
  mutex-protected registry `STPMgr* -> CManager*`. A live handle always resolves:
  a `CManager` dies only when nothing holds a reference on it, and its registry
  entry is erased first. Calls that take a `stp_tm` do not consult the registry;
  they check `GetNodeManager() == cm->bm` per term argument and report
  `FOREIGN_MANAGER` (with the term involved, when its manager is known).
- **`CManager` is the C layer's per-manager state**, refcounted by: `stp_tm`
  handles, every unscoped term reference, every open scope, every solver, model,
  array-value and function-value handle. It holds one `ManagerImpl` reference for
  its whole life, so anything reachable from a C handle keeps the manager alive,
  in any release order (tested in `c3-runtime.cpp`). The hooks `ManagerImpl`
  carries for the C layer (`c_error`, `c_error_callback`, `c_error_user`,
  `c_scopes`) and `SolverImpl::failed` are therefore **unused**; nothing in
  `Internal.h` was changed.
- **Two external counts per node** (the sketch's rules 1-4) without engine
  support: an unscoped reference is one engine `IncRef` plus one entry in
  `CManager::unscoped` (`ASTInternal* -> count`); a scoped reference is an
  `ASTNode` in the innermost journal (`CManager::scopes`), whose destructor is
  the release. Rule 3 (`stp_term_release` of a scoped handle is `STATE`) needs
  the count table, so an export while no scope is open costs one hash-table
  operation, where the sketch hoped for "no hash lookup". Engine-side counters
  would remove it; nothing in the public contract depends on it.
- **Sorts are pooled by the manager**: `stp_sort` is a `CSort{cm, index}` owned
  by `CManager::sorts` (one per interned sort index), valid while the manager
  lives, pinning nothing. `stp_sort_copy` returns the same handle,
  `stp_sort_release` is a no-op (the sketch allows this: "release is optional,
  sorts are pooled"). Consequently `stp_tm_release_all` releases term references
  only.
- **Error records**: `ErrorRecord` holds the strings behind the public
  `stp_error` view. `view.function` is always one of this layer's string
  literals (the C function name), so `function` names the **C** function that
  refused while `message` carries the C++ text, which names the C++ method
  (`invalid call to 'TermManager::mk_bv': ... [VALUE_OUT_OF_RANGE]`). A record
  never moves after `set`; on allocation failure while recording, the view falls
  back to a static RESOURCE text. The first error since the last clear is kept;
  the callback sees every error (its `stp_error*` is valid during the call
  only).
- **Where a `NULL` goes**: a `NULL` term or sort propagates silently (the
  converters throw `NullArgument`, which the boundary turns into the failure
  value with no record). A `NULL` object handle (manager, solver, options,
  model, value, statistics) is `NULL_HANDLE` in the **thread-local** record
  (`stp_last_error`); a `NULL` string or out-pointer is `NULL_HANDLE` in the
  object's record, with the argument index. `stp_solver_assert(s, NULL)` records
  `NULL_HANDLE` and fails the solver, as the sketch asks.
- **The failed state** is `CSolver::failed`, set by `solver_mutate` (assert,
  push, pop, parse*, reset*, every option write and `stp_solver_reset_option`)
  and honoured by `solver_checked` (`check_sat*`, `entails`, `write_cnf`,
  `model`, `candidate_model`, `value`), which refuses with `STATE` whose message
  names the original failure. `write_cnf` and `candidate_model` are additions to
  the sketch's list: both run or read a check, so a dropped assertion would
  falsify them too. Reads (`assertions`, `to_smt2`, `statistics`, option
  getters, `unsat_assumptions`) work in the failed state; a later successful
  mutation does not clear it, only `stp_solver_clear_error`.
- **Every `extern "C"` body runs inside `guarded`**: `Error` -> its code,
  `std::bad_alloc` -> `RESOURCE`, any other exception -> `INTERNAL`. Nothing
  propagates. `stp_solver_interrupt`, `stp_solver_clear_interrupt` and
  `stp_solver_interrupt_pending` bypass the boundary, the registry and every
  allocation, so they stay usable from another thread and from a signal
  handler.

## Deviations from the sketch

1. **`STP_API`** also honours `STP_EXPORTS`, the macro the build of libstp
   defines (the sketch named only `STP_BUILDING`; both work).
2. **The enums** `stp_kind`, `stp_error_code` and `stp_option` come from the
   generated headers `<stp/api/gen/{kinds,errors,options}.h>` instead of being
   spelled out; the rest are hand-written with the sketch's values, and
   `static_assert`s in `stp_c.cpp` pin them to the C++ enums.
3. **`stp_apply`** follows the generator, not the sketch: `stp_apply(tm, f, x)`
   is the binary form and `stp_apply_n(tm, n, args)` takes the function as
   `args[0]`. The sketch had `stp_apply(tm, f, n, args)`.
4. **Generated variants the sketch did not list**: `stp_distinct2`, `stp_xor2`,
   `stp_bvand_n`, `stp_bvor_n`, `stp_bvxor_n`, `stp_bvadd_n`, `stp_bvmul_n`,
   `stp_real_add_n` (all from `kind_ctors.h`).
5. **Functions added**: `stp_tm_uf_sort_width`, `stp_tm_scope_depth`,
   `stp_get_internal_error_policy` (the C++ getter; named with `get_` because
   `stp_internal_error_policy` is the typedef), `stp_term_same`,
   `stp_mk_term2_indexed2` (the `to_fp` shape), `stp_solver_symbol` (the sketch
   mentions it in its optional-results list but never declares it),
   `stp_option_from_name`, `stp_model_bv_num_limbs`, `stp_array_value_sort`,
   `stp_fun_value_sort`, `stp_statistics_is_double`. All `_rm` variants the
   sketch promises exist: `stp_fp_{add,sub,mul,div,fma,sqrt,rti}_rm`,
   `stp_to_fp_rm`, `stp_to_fp_unsigned_rm`, `stp_fp_to_{ubv,sbv}_rm`.
6. **`stp_statistics_name`** strings are owned by the statistics handle, not
   static: the C++ `Statistics` keys are `std::string`s in a map and the static
   spelling table is private to `Solver.cpp`.
7. **`stp_get_version`** strings are static in effect (a function-local cached
   `Version`), as the sketch requires.
8. **The error record's `function`** for a named constructor is
   `stp_mk_term`/`stp_mk_term2`: the generated `kind_ctors_c.inc` routes every
   named constructor through those two primitives, so that is the C function
   that refused. The message still names the kind.
9. **`stp_term_fits_uint64` / `stp_term_fits_int64` / `stp_term_real_fits_int64`**
   answer `false` (no record) for a term that is not a value of the right sort,
   where the C++ methods throw `NOT_A_VALUE`/`SORT_MISMATCH`: a `bool`-returning
   "fits" question has a natural false answer.
10. **`stp_solver_num_unsat_assumptions`** returns 0 and records `STATE` after a
    sat/unknown answer (the sketch's "STATE" cannot be expressed in a `size_t`).
11. **`stp_options_copy`** gives the copy a clean error record.
12. **`stp_tm_release_all`** empties the journals but keeps the scopes open
    (their push/pop balance is the caller's), as the sketch's rule 4 says.
13. **Diagnostic sink text** is copied so that `text` is NUL-terminated
    (`std::string_view` from the C++ sink is not); `len` is passed as well.
14. **`stp_set_internal_error_policy`** takes effect process-wide, exactly as the
    C++ function does (it is the same switch).

## Sketch functions not implemented

None. Every function of the sketch has a definition, with the signature
changes listed above (`stp_apply`) and the additions.

## C++-side defects and gaps met while building this

Recorded precisely as found; none blocked the layer. Reproductions are in
`tests/api/c3/` where noted, or were done with throw-away C programs against
`build-c/lib/libstp.so`.

1. **`Solver::assertions()` is not stable across checks** (`lib/Api/Solver.cpp`,
   `Solver::assertions`, reading `bm->AssertLevels()`). After two Boolean
   assertions at level 0 the first `check_sat` leaves `assertions()` at 2, but
   the **second** `check_sat` at level 0 (after a push/assert/check/pop) leaves
   it at 1: `(and a b)`. Likewise `parse_smt2` of a script that ends in
   `(check-sat)`, even under `ParseMode::DECLARE_AND_ASSERT` (which is supposed
   to ignore it), yields one conjoined assertion where the same script without
   the `(check-sat)` yields three. The engine (or `Cpp_interface`'s check-sat
   path) rewrites the assertion stack in place and the API returns the rewritten
   stack. The header promises "outermost first" of what was asserted. The C
   tests therefore only count assertions before the first check.
2. **Printing of symbols** (`Terms.cpp`, `print_term` -> the engine's SMT-LIB 2
   printer). Every symbol printed `|quoted|` (`x` printed as `|x|`), although
   `stp.hpp` says "a symbol prints as its declared name" and `Manager.cpp` has
   `quote_symbol` that quotes only where needed; and a leading constant got a
   double space: `(bvadd  #x01 (bvmul |x| |y|))`. FIXED: the unshared form
   (`stp_term_str`, `share = false`) is now the API's own printer -- bare
   simple names, bars only where SMT-LIB needs them, single spaces, lowercase
   hex; the let-sharing form is still the engine's printer and quotes every
   symbol. The C tests' bar-stripping comparison holds for both.
3. **`FP_TO_FP_FROM_REAL` needs a rounding-mode value** as well as a Real value
   (`Construct.cpp`, `fp_from_real_value`): with a symbolic mode it is
   `UNSUPPORTED` ("converting a Real to a float needs a rounding-mode value, not
   a symbolic mode"). `kinds.toml` documents the Real-value requirement only.
   Not a defect of the code, a gap in the table's note.
4. **Equality over a constant array is `UNSUPPORTED`** (documented in README.md
   and `capabilities()["array.const-equality"] = "false"`), which also refuses
   `store(k, i, v) = k`. Recorded here because it shapes the C tests: array
   results are read back through `select`, never through `=`.
5. **The SMT2 parser exit()s on an operand-count violation** -- SERIOUS, FIXED:
   the grammar unwinds to the parse entry, and every refusal of the frontend
   (a sort error, a wrong arity, a constant that does not fit) is a `PARSE`
   error now; an engine failure inside any call is `INTERNAL` and poisons the
   manager (lib/Api/README.md, "Errors"). As found: feeding
   `Solver::parse_term` (or `parse_smt2`) a term that applies an n-ary
   bit-vector operator to too few operands -- e.g. `(bvadd x)` -- prints
   `syntax error: ... Must be >=2 operands` and terminates the process with
   `exit(1)`. Every other malformed input (`x y`, an undeclared symbol,
   `#xGG`, the unbalanced `(bvadd x x x`) instead returns a recoverable `PARSE`
   error, as it should. The fatal path is uncatchable: the C layer's
   `try/catch` boundary never runs, and no error is recorded. Reproduced with a
   9-line C program against `build-c/lib/libstp.so`:
   `stp_solver_parse_term(s, "(bvadd x")` (whose `(assert (= T T))` wrapper
   makes the inner `(bvadd x)`). The trigger is the "Must be >=2 operands"
   semantic action in the SMT-LIB 2 grammar (`lib/Parser/smtlib2.y`), which must
   call the recoverable parse-error path rather than `FatalError`/`exit`. Until
   the C++ side is fixed the C tests avoid arity-underflow inputs; a client that
   parses untrusted SMT can still be killed by one.
6. **`bind_symbol` of a compound term poisons every later parse** -- SERIOUS,
   FIXED (`bind_symbol` takes a symbol only; and a `FatalError` reached
   through a parse is an `INTERNAL` error rather than an abort). As found:
   `TermManager::bind_symbol` (`lib/Api/Manager.cpp:1052`) accepts any term and
   pushes its name onto `symbol_order`, but `seed_parser_symbols`
   (`lib/Api/Solver.cpp`) walks `symbol_order` before every parse and calls
   `Cpp_interface::addSymbol` on each node, which calls `ASTNode::GetName`.
   `GetName` on a non-SYMBOL node is a `FatalError` -> `abort()`. So
   `bind_symbol("s", bvadd(x, y))` succeeds, and the next `parse_smt2` /
   `parse` / `parse_term` / `parse_file` on that manager aborts the process with
   SIGABRT (exit 134). Reproduced with a 12-line C program. Either
   `bind_symbol` should reject a non-symbol term (the design frames it as
   aliasing a symbol, §5.5), or `seed_parser_symbols` should seed only nodes
   whose kind is `SYMBOL`. The C test aliases a genuine symbol, bind_symbol's
   documented use, and never binds a compound term before a parse.
