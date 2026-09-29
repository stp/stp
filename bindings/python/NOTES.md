# The Python layer: implementation notes

`bindings/python/stp` is the Python API, a z3py-style package over the C API
`<stp/stp.h>`. This file records how the layer is built and the decisions
that depart from z3py or from a literal reading of the C API.

## Files

| file | contents |
|---|---|
| `stp/_core.pxd` | the C API as Cython sees it; includes the generated `_gen_enums.pxi` |
| `stp/_core.pyx` | the Cython extension `stp._core`: handle classes (`Manager`, `Sort`, `Term`, `OptionsHandle`, `SolverHandle`, `ModelHandle`, `ArrayValueHandle`, `FunValueHandle`, `StatisticsHandle`), the exception hierarchy and the error translator, the deferred-release queue, the GIL-free checks and parsers, the SIGINT bridge, the registry queries |
| `stp/_terms.py` | `TermManager`, the sort classes, the `ExprRef` family with the operator ledger and literal coercion, every sort and term builder |
| `stp/_solver.py` | `Options`/`OptionInfo`, `CheckSatResult`/`EntailmentResult`, `Statistics`, `Solver`, `Model`, `SolverFor`, `solve`, `prove`, `parse_smt2_*`, the current-solver scope and the 2.x `@stp` decorator |
| `stp/_pretty.py` | `str(term)`: the infix rendering |
| `stp/_smt2.py` | pickling and `translate()` of sorts, terms and models; the s-expression reader behind `Model.from_smt2` |
| `stp/__init__.py` | the public names, `__all__`, `version()`, `capabilities()` |
| `CMakeLists.txt` | `ENABLE_PYTHON_API` (ON when `PYTHON_EXECUTABLE` can import Cython); cythonises at build time, builds `_core` with `Python3_add_library`, assembles the package in `<build>/bindings/python/stp/` |
| `../../tests/api/python/` | the pytest suite, registered as the CTest entry `python-api-tests` (labels `python`, `api`) |

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
  function), `.argument_index`, `.option` and `.terms` (each in its own
  manager's wrapper: a FOREIGN_MANAGER error names the other manager's term),
  and cleared. Calls with
  no manager read `stp_last_error()`. A failed *mutation* of a solver also
  leaves the solver's failed state at once (`stp_solver_clear_error`): a raised
  exception cannot be ignored, so Python needs no failed state. `ParseError.lineno/offset` are parsed from the message
  (`parse error at L:C`).
- **Threads.** A `Manager` and everything created from it may be used from
  any thread, one call at a time: the GIL serialises the
  Python entry points, and while one of the calls that release it
  (`stp_solver_check_sat_budget`, `stp_solver_entails`, the parsers and
  `stp_solver_write_cnf`) runs, a call on the same manager from another
  thread raises `StateError` (the manager records the thread it is busy on).
  `Solver.close()` from another thread then interrupts the solver and defers
  its delete until the call returns, as the garbage collector would. The
  deferred releases are kept per manager, so a drain looks at the idle
  managers' only. `Solver.interrupt()` (which
  takes no lock) may be called from any thread at any time and reaches a
  running check. On the main thread a C `SIGINT` handler is installed for the
  duration of a check: it calls `stp_solver_interrupt` and, after the check,
  Python's own handler is restored and the signal re-delivered
  (`PyErr_SetInterrupt`), so Ctrl-C raises `KeyboardInterrupt` from `check()`
  and the solver stays usable (around a parse that runs its input as well).
  A user terminator (`set_terminator`) runs with the GIL; an exception it
  raises interrupts the check and is re-raised. Parses take one process-wide
  lock for their whole length, so a parse on another manager waits for one
  that is checking or waiting on its stream. A callback (a sink, the
  terminator, the stream a parse reads) must not call the library: every call
  from one raises `StateError`, but `interrupt()`, `clear_interrupt()` and
  `interrupt_pending()`.
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

1. **The class layer is pure Python.** The extension holds the handles and
   the shell holds the classes (the `ExprRef` family, `Solver`, `Model`, the
   operators), so the per-term path is Python.
2. **`Model.__getitem__` on an array value returns an `ArrayNumRef` view**
   built from `stp_model_array_value`; `v[i]` for a symbolic `i` builds
   `Select(v, i)` over the value's store chain on a constant array, and stays
   a `SELECT` (only a read of the constant array itself folds, to its default,
   `lib/Api/README.md`).
3. **`Model.__getitem__` never completes**: it is `stp_model_try_value`, which
   refuses every term whose value would need completion, and its `KeyError`
   names the symbols outside the core (`m.eval(t)` completes).
4. **`Model.eval(t, model_completion=False)`** substitutes the core's *scalar
   and array* values and leaves applications of function symbols in place: no
   term stands for a function value.
5. **Pickling and `translate(tm)` of terms are structural**, not SMT-LIB text:
   `(kind, indices, result sort, children)` with values as their printed text
   and symbols as `(name, sort text)`, rebuilt through the target manager's
   name table (`tm.declare` gives the same term for the same name and sort).
   Text would not do: a value of a declared sort prints as `S!k`, which the
   parser does not read back. Consequences: an anonymous (`mk_fresh`) symbol
   and a value of an uninterpreted sort raise `Unsupported` when pickled or
   translated (they have no name to rebuild by).
6. **`Model.from_smt2` / `Model.__reduce__` / `Model.translate`** rebuild a
   model by reading the printed `define-fun`s with a small s-expression reader,
   declaring the symbols by name and asking a solver for a model of the
   equalities that pin their values (arrays cell by cell, functions case by
   case, values of a declared sort up to the (dis)equalities among the symbols
   of that sort). There is no `stp_model_*` constructor from values. What is
   not preserved: array defaults and function `else` values other than the
   sort default (they come from the solver's fill rule, which for STP is the
   sort default unless `model-array-fill = ones`).
   The model is built on `tm` (a private manager when `tm` is `None`) by a
   scratch solver of its own, and the solvers already live over `tm` are
   untouched; lookups translate their key by name, so `m2[x]` works whichever
   manager `x` belongs to.
7. **`bool(term)`** is defined for a ground Bool term only: it folds with
   `stp_tm_simplify`, so the answer never depends on the manager's `simplify`
   setting, and a Python evaluator decides `distinct` and `=`, the Bool
   connectives, `ite` and the Real relations over values should the fold leave
   one of them alone. Any other term raises `TypeError`, as does one whose
   value an unspecified floating-point case decides (`fpMin` of the two zeros,
   `fpToUBV` of NaN, ...), which is a check's to choose.
8. **`str(term)`** is a best-effort infix rendering (values as Python
   literals, symbols by name, `If`, `Extract`, `f(x)`, `a[i]`, ...); `repr`
   is the SMT-LIB 2 text of `stp_term_str`. `to_string("smtlib2")` is
   `sexpr()`.
9. **`RotateLeft(a, b)` / `RotateRight(a, b)` with a term amount** are built
   from shifts (the kind table has no term-amount rotate), the amount taken
   modulo the size as an int amount is; with an int amount the indexed kind
   is built, which the engine represents as a concatenation
   of extracts (the public view of `RotateLeft(x, 3).kind()` is `BV_CONCAT`).
10. **`Solver(tm, options, **kw)`** also accepts a `dict` for `options`;
    `Solver.dimacs()` (the DIMACS text as a `str`) and `Solver.last_result()`
    are additions; `Solver.value(t)` is `model()[t]` (KeyError for a symbol
    outside the core).
11. **`solve()`, `prove()` and `parse_smt2_string`** each run in a scratch
    solver of their own on the formulas' manager and close it; the solvers
    already live there are untouched, and a script's declarations stay in the
    name table.
12. **`TermManager(options=...)`** takes the manager-scoped entries from an
    `Options` object (or an `OptionsHandle`); `simplify=`/`default_rounding_mode=`
    override it. `main_tm()` is created lazily under a lock; `set_main_tm`
    replaces it (the test suite does this per test).
13. **`Statistics`** is registered with `collections.abc.Mapping` over the
    snapshot the solver took; `tier(name)` answers for every name of the
    table.
14. **`UnknownReason`** members compare equal to their string values and hash
    like them; `CheckSatResult.__eq__` also compares an unknown check result
    equal to an unknown `EntailmentResult`, so the one `unknown` serves both.
15. **The `@stp` decorator** keeps the 2.x rules (arguments not supplied become
    32-bit symbols named `<function>_<call>_<arg>`; a default value is the
    width; `assert` adds to the current solver; `return` gives the term) and
    adds assignments, unary operators and chained comparisons. It needs
    `solver_scope(s)` to be active (`StateError` otherwise).
16. **`Kind.smtlib`** is attached to the generated enum at import
    (`_gen_kinds.py` is generated without the property).
17. **Installation:** this package is the installed `stp`, and STP's only
    Python package (the 2.x ctypes one is gone). pip also installs it on its
    own against an installed STP (`pyproject.toml`, `setup.py`; `README.md`
    says how): the install ships the generated `_gen_enums.pxi` and
    `_gen_kinds.py` in `include/stp/api/python` for that build. Not done:
    wheels, doctests, a generated `.pyi` stub.
