# The C layer: implementation notes

`include/stp/stp.h` is the C face of the C++ API in `include/stp/stp.hpp`.
This file records how its runtime is built and the decisions the header
leaves to the implementation.

## Files

| file | contents |
|---|---|
| `stp_c_internal.h` | the runtime structures: `CManager` (per-manager state), the handle structs, `ErrorRecord`, the exception boundary `guarded`, the solver's `solver_mutate`/`solver_checked` |
| `stp_c.cpp` | managers, reference counts, scopes, the error record and callback, the library queries, sorts, symbols, values, generic and named construction (includes the generated `kind_ctors_c.inc`), term introspection and readers |
| `stp_c_options.cpp` | standalone `stp_options`, the registry introspection, the live options of a solver |
| `stp_c_solver.cpp` | solver, model, array/function values, statistics |

## How the runtime is built

- **A term handle is the engine node** (`ASTInternal*`).
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
- **Two external counts per node** (the header's ownership rules 1-4) without engine
  support: an unscoped reference is one engine `IncRef` plus one entry in
  `CManager::unscoped` (`ASTInternal* -> count`); a scoped reference is an
  `ASTNode` in the innermost journal (`CManager::scopes`), whose destructor is
  the release. Rule 3 (`stp_term_release` of a scoped handle is `STATE`) needs
  the count table, so an export while no scope is open costs one hash-table
  operation where none would be ideal. Engine-side counters
  would remove it; nothing in the public contract depends on it.
- **Sorts are pooled by the manager**: `stp_sort` is a `CSort{cm, index}` owned
  by `CManager::sorts` (one per interned sort index), valid while the manager
  lives, pinning nothing. `stp_sort_copy` returns the same handle,
  `stp_sort_release` is a no-op (the header allows this: "release is optional,
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
  `NULL_HANDLE` and fails the solver.
- **The failed state** is `CSolver::failed`, set by `solver_mutate` (assert,
  push, pop, parse*, reset*, every option write and `stp_solver_reset_option`)
  and honoured by `solver_checked` (`check_sat*`, `entails`, `write_cnf`,
  `model`, `candidate_model`, `value`), which refuses with `STATE` whose message
  names the original failure. `write_cnf` and `candidate_model` are additions to
  that list: both run or read a check, so a dropped assertion would
  falsify them too. Reads (`assertions`, `to_smt2`, `statistics`, option
  getters, `unsat_assumptions`) work in the failed state; a later successful
  mutation does not clear it, only `stp_solver_clear_error`.
- **Every `extern "C"` body runs inside `guarded`**: `Error` -> its code,
  `std::bad_alloc` -> `RESOURCE`, any other exception -> `INTERNAL`. Nothing
  propagates. `stp_solver_interrupt`, `stp_solver_clear_interrupt` and
  `stp_solver_interrupt_pending` bypass the boundary, the registry and every
  allocation, so they stay usable from another thread and from a signal
  handler.

## Decisions of the implementation

1. **`STP_API`** follows the engine's `DLL_PUBLIC` convention: on Windows it
   is a `__declspec` only when libstp is a DLL (`STP_SHARED_LIB`), `dllexport`
   while the API's own objects are compiled (`STP_API3_BUILDING`, not
   `STP_EXPORTS`, which libstp2 defines too) and `dllimport` otherwise.
2. **The enums** `stp_kind`, `stp_error_code` and `stp_option` come from the
   generated headers `<stp/api/gen/{kinds,errors,options}.h>` instead of being
   spelled out; the rest are hand-written, and
   `static_assert`s in `stp_c.cpp` pin them to the C++ enums.
3. **`stp_apply`** follows the generator: `stp_apply(tm, f, x)`
   is the binary form and `stp_apply_n(tm, n, args)` takes the function as
   `args[0]`.
4. **Generated variants**: `stp_distinct2`, `stp_xor2`,
   `stp_bvand_n`, `stp_bvor_n`, `stp_bvxor_n`, `stp_bvadd_n`, `stp_bvmul_n`,
   `stp_real_add_n` (all from `kind_ctors.h`).
5. **Functions added**: `stp_tm_uf_sort_width`, `stp_tm_scope_depth`,
   `stp_get_internal_error_policy` (the C++ getter; named with `get_` because
   `stp_internal_error_policy` is the typedef), `stp_term_same`,
   `stp_mk_term2_indexed2` (the `to_fp` shape), `stp_solver_symbol`,
   `stp_option_from_name`, `stp_model_bv_num_limbs`, `stp_array_value_sort`,
   `stp_fun_value_sort`, `stp_statistics_is_double`. Every `_rm` variant exists: `stp_fp_{add,sub,mul,div,fma,sqrt,rti}_rm`,
   `stp_to_fp_rm`, `stp_to_fp_unsigned_rm`, `stp_fp_to_{ubv,sbv}_rm`.
6. **`stp_statistics_name`** strings are owned by the statistics handle, not
   static: the C++ `Statistics` keys are `std::string`s in a map and the static
   spelling table is private to `Solver.cpp`.
7. **`stp_get_version`** strings are static in effect (a function-local cached
   `Version`).
8. **The error record's `function`** for a named constructor is
   `stp_mk_term`/`stp_mk_term2`: the generated `kind_ctors_c.inc` routes every
   named constructor through those two primitives, so that is the C function
   that refused. The message still names the kind.
9. **`stp_term_fits_uint64` / `stp_term_fits_int64` / `stp_term_real_fits_int64`**
   answer `false` (no record) for a term that is not a value of the right sort,
   where the C++ methods throw `NOT_A_VALUE`/`SORT_MISMATCH`: a `bool`-returning
   "fits" question has a natural false answer.
10. **`stp_solver_num_unsat_assumptions`** returns 0 and records `STATE` after a
    sat/unknown answer (`STATE` cannot be expressed in a `size_t`).
11. **`stp_options_copy`** gives the copy a clean error record.
12. **`stp_tm_release_all`** empties the journals but keeps the scopes open
    (their push/pop balance is the caller's), as ownership rule 4 says.
13. **Diagnostic sink text** is copied so that `text` is NUL-terminated
    (`std::string_view` from the C++ sink is not); `len` is passed as well.
14. **`stp_set_internal_error_policy`** takes effect process-wide, exactly as the
    C++ function does (it is the same switch).
