# The Python layer: implementation notes

`bindings/python3/stp` is the Python API, a z3py-style package over the C API
`<stp/stp.h>`. This file records how the layer is built, the decisions that
depart from z3py or from a literal reading of the C API, what the C API did
not offer, and every defect of the C or C++ layers met on the way.

## Files

| file | contents |
|---|---|
| `stp/_core.pxd` | the C API as Cython sees it; includes the generated `_gen_enums.pxi` |
| `stp/_core.pyx` | the Cython extension `stp._core`: handle classes (`Manager`, `Sort`, `Term`, `OptionsHandle`, `SolverHandle`, `ModelHandle`, `ArrayValueHandle`, `FunValueHandle`, `StatisticsHandle`), the exception hierarchy and the error translator, the deferred-release queue, the GIL-free checks and parsers, the SIGINT bridge, the registry queries |
| `stp/_terms.py` | `TermManager`, the sort classes, the `ExprRef` family with the operator ledger and literal coercion, every builder of the stub |
| `stp/_solver.py` | `Options`/`OptionInfo`, `CheckSatResult`/`EntailmentResult`, `Statistics`, `Solver`, `Model`, `SolverFor`, `solve`, `prove`, `parse_smt2_*`, the current-solver scope and the 2.x `@stp` decorator |
| `stp/_pretty.py` | `str(term)`: the infix rendering |
| `stp/_smt2.py` | pickling and `translate()` of sorts, terms and models; the s-expression reader behind `Model.from_smt2` |
| `stp/__init__.py` | the public names, `__all__`, `version()`, `capabilities()` |
| `CMakeLists.txt` | `ENABLE_PYTHON3_API` (ON when `PYTHON_EXECUTABLE` can import Cython); cythonises at build time, builds `_core` with `Python3_add_library`, assembles the package in `<build>/bindings/python3/stp/` |
| `../../tests/api/python3/` | the pytest suite, registered as the CTest entry `python3-api-tests` (labels `python3`, `api3`) |

## How the layer is built

- **Two layers, one contract.** `_core` owns every C handle and does the
  error translation; the z3py-flavoured classes (`ExprRef`, `BitVecRef`,
  `Solver`, `Model`, ...) are pure-Python subclasses of the `cdef` classes,
  registered with the core at import (`register_term_classes`,
  `register_sort_classes`, `register_value_classes`) so that every wrapper the
  core mints is already of the right Python class, chosen from the term's sort
  and `stp_term_is_value`.
- **One wrapper per live node.** `Manager._wrap` keeps a `WeakValueDictionary`
  from node id to wrapper: a second handle to a node already wrapped is
  released and the existing object returned, so `a is b` iff the terms are the
  same. Sorts are pooled the same way (they are pooled by the manager anyway).
  `ArrayNumRef` (the mapping view of an array value) is the one deliberate
  second wrapper of a node (`Manager.rewrap`): it decorates the store chain with
  the `stp_array_value` handle.
- **Errors.** After a failing call the manager's record is read, turned into
  the exception class of its code (the table of `errors.toml`), decorated with `.code`, `.recoverable`, `.function` (the C
  function), `.argument_index`, `.option` and `.terms`, and cleared. Calls with
  no manager read `stp_last_error()`. A failed *mutation* of a solver also
  leaves the solver's failed state at once (`stp_solver_clear_error`): a raised
  exception cannot be ignored, so Python needs no failed state. `ParseError.lineno/offset` are parsed from the message
  (`parse error at L:C`).
- **Threads.** A `Manager` and everything created from it may be used from
  any thread, one call at a time: the GIL serialises the
  Python entry points, and the calls that release it
  (`stp_solver_check_sat_budget`, `stp_solver_entails`, the parsers and
  `stp_solver_write_cnf`) must not overlap another call on the same manager,
  which is the caller's business, as it is in C++. `Solver.interrupt()` (which
  takes no lock) may be called from any thread at any time and reaches a
  running check. On the main thread a C `SIGINT` handler is installed for the
  duration of a check: it calls `stp_solver_interrupt` and, after the check,
  Python's own handler is restored and the signal re-delivered
  (`PyErr_SetInterrupt`), so Ctrl-C raises `KeyboardInterrupt` from `check()`
  and the solver stays usable. A user terminator (`set_terminator`) runs with
  the GIL; an exception it raises interrupts the check and is re-raised.
- **Deferred release.** Node reference counts are plain. A wrapper finalised
  while its manager is inside a check (`Manager.busy`), or after the cyclic
  garbage collector already cleared its manager reference, does not release
  its handle: the handle goes onto a process-wide queue tagged with its manager
  (kept in a C field, so it survives `tp_clear`), and the next entry point of
  any manager, on whichever thread, releases every queued handle whose manager
  is not busy at that moment. A finaliser that runs while the manager is idle
  releases at once, from any thread: the GIL serialises it with every other
  use of the manager.
- **Options.** `Options` is a mapping over the registry (names, `python_key`s
  with `-` and `.` as `_`, the aliases, z3py's `timeout`); the type of the
  registry entry picks the typed setter (`bool`, `int`/`uint`, `duration` in
  ms / `timedelta` / `"500ms"`, `mode` from `True`/`False`/`"auto"`, `set` from
  a list, `RoundingMode` members by name). `Solver.options` is the live view:
  the same class over a `_LiveBackend` that calls the solver's `stp_solver_*`
  option functions, where the entry's Settable window is enforced by the C
  layer (`OPTION_TIMING`).

## Decisions of the implementation

1. **The class layer is pure Python.** The plan
   puts the `ExprRef` family, `Solver`, `Model` and the operators in the
   Cython extension; here the extension holds the handles and the shell holds
   the classes. Behaviour is the stub's; the per-term path is Python.
2. **`Model.__getitem__` on an array value returns an `ArrayNumRef` view**
   built from `stp_model_array_value`; `v[i]` for a symbolic `i` builds
   `Select(v, i)` over the value's store chain on a constant array, and stays
   a `SELECT` (only a read of the constant array itself folds, to its default,
   `lib/Api/README.md`).
3. **`Model.__getitem__` enforces the no-completion rule itself** for compound
   terms and array symbols, because `stp_model_try_value` completes them (C++
   defect 6 below); a core symbol or a value takes the fast path.
4. **`Model.eval(t, model_completion=False)`** substitutes the core's *scalar
   and array* values and leaves applications of function symbols in place: no
   term stands for a function value.
5. **Pickling and `translate(tm)` of terms are structural**, not SMT-LIB text:
   `(kind, indices, result sort, children)` with values as their printed text
   and symbols as `(name, sort text)`, rebuilt through the target manager's
   name table (`tm.declare` gives the same term for the same name and sort).
   The parser cannot read several value forms its own printer emits (C++
   defect 4), so text was not an option. Consequences: an anonymous
   (`mk_fresh`) symbol and a value of an uninterpreted sort raise
   `Unsupported` when pickled or translated (they have no name to rebuild by).
6. **`Model.from_smt2` / `Model.__reduce__` / `Model.translate`** rebuild a
   model by reading the printed `define-fun`s with a small s-expression reader,
   declaring the symbols by name and asking a solver for a model of the
   equalities that pin their values (arrays cell by cell, functions case by
   case, values of a declared sort up to the (dis)equalities among the symbols
   of that sort). There is no `stp_model_*` constructor from values. What is
   not preserved: array defaults and function `else` values other than the
   sort default (they come from the solver's fill rule, which for STP is the
   sort default unless `model-array-fill = ones`), and the `observed` flags.
   The model is built on `tm` when `tm` has no live solver, and on a private
   manager otherwise (the alpha's one-solver rule, and the live solver carries
   the user's assertions); lookups translate their key by name, so `m2[x]`
   works whichever manager `x` belongs to.
7. **`bool(term)`** first folds with `stp_tm_simplify`; when the rewriter leaves
   a ground shape alone (C++ defect 3), a Python evaluator decides `distinct`
   and `=` over values, the Bool connectives and `ite` over values, and the
   Real relations over values. `bool()` of a ground FP conversion such as
   `fpToSBV` of a value still raises: evaluate it in a model.
8. **`str(term)`** is a best-effort infix rendering (values as Python
   literals, symbols by name, `If`, `Extract`, `f(x)`, `a[i]`, ...); `repr`
   is SMT-LIB 2 with the printer's double spaces collapsed (C NOTES defect 2).
   `to_string("smtlib2")` is `sexpr()`.
9. **`RotateLeft(a, b)` / `RotateRight(a, b)` with a term amount** are built
   from shifts (the kind table has no term-amount rotate); with an int amount
   the indexed kind is built, which the engine represents as a concatenation
   of extracts (the public view of `RotateLeft(x, 3).kind()` is `BV_CONCAT`).
10. **`Solver(tm, options, **kw)`** also accepts a `dict` for `options`;
    `Solver.dimacs()` (the DIMACS text as a `str`) and `Solver.last_result()`
    are additions; `Solver.value(t)` is `model()[t]` (KeyError for a symbol
    outside the core, as the stub says).
11. **`solve()` and `prove()`** on a manager that already carries its one live
    solver run in a scratch manager the formulas are translated into;
    `parse_smt2_string` on such a manager parses under `push`/`pop` of the
    live solver (its declarations stay in the name table, as they should).
12. **`TermManager(options=...)`** takes the manager-scoped entries from an
    `Options` object (or an `OptionsHandle`); `simplify=`/`default_rounding_mode=`
    override it. `main_tm()` is created lazily under a lock; `set_main_tm`
    replaces it (the test suite does this per test).
13. **`Statistics`** is registered with `collections.abc.Mapping`; the snapshot
    holds only the statistics the last check populated (49 of the 63 names),
    `tier(name)` answers for every table name.
14. **`UnknownReason`** members compare equal to their string values and hash
    like them; `CheckSatResult.__eq__` also compares an unknown check result
    equal to an unknown `EntailmentResult` (the stub's `unknown`).
15. **The `@stp` decorator** keeps the 2.x rules (arguments not supplied become
    32-bit symbols named `<function>_<call>_<arg>`; a default value is the
    width; `assert` adds to the current solver; `return` gives the term) and
    adds assignments, unary operators and chained comparisons. It needs
    `solver_scope(s)` to be active (`StateError` otherwise).
16. **`Kind.smtlib`** is attached to the generated enum at import
    (`_gen_kinds.py` is generated without the property).
17. **Installation:** this package is the installed `stp` (the 2.x ctypes
    package, which has the same name, is built for its libstp2 tests only).
    pip also installs it on its own against an installed STP
    (`pyproject.toml`, `setup.py`; `README.md` says how): the install ships
    the generated `_gen_enums.pxi` and `_gen_kinds.py` in
    `include/stp/api/python` for that build. Not done: wheels, doctests, a
    generated `.pyi` stub.

## C API gaps met while building this

1. No way to construct a `stp_model` from values, hence deviation 6.
2. `stp_statistics_tier` reports an unknown name through the thread-local
   record, which nothing clears on success; the Python wrapper plants a
   sentinel error (`stp_option_info_type` of an impossible name) before the
   call to tell a fresh failure from a stale record.
3. `stp_solver_num_unsat_assumptions` records `STATE` and returns 0 after a
   sat/unknown answer (C NOTES deviation 10): the wrapper checks the record
   after the call.
4. No term-amount rotate kind (deviation 9).
5. Every `stp_solver_*` option function lives on the solver handle; the live
   `Options` view is an adapter over them (no options handle exists for the
   live view, by design).
6. `stp_solver_parse_file` reports a missing file as `IO`; a malformed CVC
   file kills the process instead (C++ defect 2).
7. `stp_sort_id` returned 0 for the Bool sort (its pool index), the value the
   header reserves for a NULL handle. FIXED: sort ids are 1-based now, so 0
   is never a sort id; the Python layer keys its sort cache by the id and
   exposes it as `SortRef.id`.

## C++-side defects and gaps met while building this

Recorded precisely as found; reproductions are in `tests/api/python3/` where
noted, or were done with throw-away programs against `build-py/lib/libstp.so`.

1. **Two managers on two threads corrupt the heap** -- SERIOUS, FIXED. After a
   `stp_tm_new` on one thread, a second `stp_tm_new` on another thread works,
   `stp_declare` on it works, but its first `stp_mk_bv_uint64` dies inside
   glibc (`malloc.c: sysmalloc: assertion failed: (old_top == initial_top (av)
   && old_size == 0) || ...`). It does not matter whether the first manager
   holds terms, or has already been released (`stp_tm_release_all` +
   `stp_tm_release` before the second thread starts); only a process in which
   *no* manager was created on another thread is fine. Same thread, any
   number of managers: fine. Reproduced with a 20-line C program (pthreads,
   `stp_tm_new` on `main`, then a worker doing `stp_tm_new` +
   `stp_mk_bv_uint64(tm2, 8, 3)`), and from Python. The API
   promises "independent managers are fully concurrent"; this is a
   thread-local or global in the constant path (`TermManager::mk_bv` ->
   `ASTBVConst` / the CONSTANTBV library) rather than a data race, since the
   two threads never run concurrently in the reproduction.
   `test_threads.py::test_independent_managers_on_two_threads` runs the
   scenario in a subprocess; it was `xfail(strict=True)` until the engine
   was fixed (CONSTANTBV keeps its constants in thread-locals, and the
   manager constructor now boots the library on every thread that creates a
   manager) and passes now.
2. **The CVC parser aborts on a syntax error** -- SERIOUS, FIXED: the CVC and
   SMT-LIB 1 grammars report and return, the SMT-LIB 2 grammar's fatal paths
   named below (`set-logic ALL`, `declare-sort` without a UF logic, the arity
   underflow, and every other refusal of the frontend) are `ParseError` now,
   and an engine failure inside any call is `InternalError` with the manager
   poisoned. As found: `lib/Parser/cvc.y`
   `yyerror` (line 58) calls `FatalError`, so `stp_solver_parse(text,
   STP_FORMAT_CVC)` of malformed input (an input without a `QUERY`, a typo)
   terminates the process (`Fatal Error: CVC syntax error: line 1: syntax
   error`); the C layer's boundary never runs and `Solver.from_string(...,
   format="cvc")` cannot be made safe from Python. The SMT-LIB 2 grammar has
   the same fatal path for `(set-logic ALL)` ("unsupported logic ... token:
   ALL" -> abort) and for `(declare-sort T 0)` without a UF logic ("unknown
   sort (not built in, and not a declared sort)" -> abort), in addition to the
   arity-underflow case of C NOTES defect 5. The Python tests use well-formed
   inputs only.
3. **`TermManager::simplify` leaves ground terms unfolded** (`lib/Api`,
   `stp_tm_simplify`): `(distinct true false)`, `(not (distinct true false))`,
   `(< (/ 1 3) (/ 1 2))` and the other Real relations over values,
   `((_ fp.to_sbv 8) RTZ <value>)`, `fp.to_ubv`, `fp.min`/`fp.max` over
   values stay as they are, while `(= true false)`, `xor`, Real `=`/`+`/`*`,
   `fp.add`/`fp.sqrt`/`fp.roundToIntegral`/`fp.eq`/`fp.lt`, `bvult`, `ite`
   and the bit-vector arithmetic fold. Deviation 7 covers the Bool and Real
   cases in Python; the FP conversions need a model.
4. **The SMT-LIB 2 parser did not read the value forms the printers emit.**
   FIXED except for declared-sort values: an API parse enables every
   theory's keywords without a `set-logic`, so `(fp #b0 #b... #b...)`,
   `(_ +zero 8 24)`, `(_ NaN 8 24)`, `RNE`, `fp.add`, `(/ 1 3)`, `(- 3)`,
   `1.5` and `((as const (Array ...)) v)` all parse. A declared-sort value
   such as `S!1` still does not, so a model over declared sorts cannot
   round-trip through the parser (hence deviations 5 and 6).
5. **Parse errors are echoed to stdout.** Every recoverable `PARSE` error also
   prints `(error "syntax error: ...")` on the process's stdout, and
   `(get-model)` in `DECLARE_AND_ASSERT` mode prints `unsupported` there
   (`lib/Parser/smt2.y`, `Cpp_interface`), where nothing should write to
   stdout unless a sink says so. FIXED for declare-and-assert parses (the
   default): the frontend's stdout is captured there and the diagnostic is
   the error's text; a script run in execute mode still prints its
   responses, errors included, as the command line does.
6. **`Model::try_value` completes array symbols and unseen function
   applications** (`lib/Api/Model.cpp`): for a scalar symbol outside the core
   it returns nothing (correct), for an array symbol outside the core it
   returns the symbol itself and for `g(x)` with `g` never seen it returns
   `#x00`; `in_core` answers false for both. Deviation 3 restores the mapping
   rule in Python.
7. **A `define-fun` name is not in the name table**: after
   `(define-fun dfx () (_ BitVec 8) #x07)` both `stp_tm_symbol(tm, "dfx")` and
   `stp_solver_symbol(s, "dfx")` return NULL, although the API
   says symbols a script declares are reachable through `Solver::symbol`.
   `(declare-fun ...)` names are reachable. Minor.
8. **Arrays cannot hold Bools**: `stp_mk_array_sort(tm, bv, bool)` is
   `UNSUPPORTED` ("bit-vectors, floating-point numbers, rounding modes and
   declared sorts only", `capabilities: array.element-sorts`). Documented by
   `capabilities()`, recorded here because the stub's `Array(name, index,
   element)` reads as unrestricted.
9. C NOTES defects 1 (assertion count after a check), 2 (`|x|` and the double
   space before constants; fixed since, simple names now print bare), 4
   (equality over a constant array; fixed since, `test_const_arrays.py`) were
   met again and shaped the tests: the rosetta R4 `b == c` is now stated directly,
   assertion counts are checked before checks, printed symbols are compared
   by name.
