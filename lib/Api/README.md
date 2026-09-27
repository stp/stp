# The STP 3.x API (alpha)

This directory implements the API designed in `api-3x/design/DESIGN.md` (in the
`master` worktree): `<stp/stp.hpp>` is the primary, C++17 surface; `<stp/stp.h>`
is the C layer over it; `stp._core` (Cython) is the Python layer over the C layer;
`libstp2` re-implements the 2.x `c_interface.h` over `stp.h`.

## Layout

| path | contents |
|---|---|
| `tables/*.toml` | the single-source tables: kinds (102), options (238), errors (21), statistics (63) |
| `gen/generate.py` | writes every generated fragment into `<build>/generated/` (C++ and C enums, named constructors, registry rows, Cython enums) |
| `Internal.h` | the private structures: `ManagerImpl`, `SolverImpl`, `ModelSnapshot`, `OptionsImpl` |
| `Errors.cpp` | exception classes, throw helpers, enum spellings |
| `Manager.cpp` | `TermManager`, `Sort`, sorts/symbols/literal values over `STPMgr` |
| `Terms.cpp` | `Term`: the public view of an engine node, typed readers, printing, substitution |
| `Construct.cpp` | `build_term`: type checking for every kind and its mapping onto engine nodes; named constructors, literal helpers, operators |
| `Options.cpp` | the registry, `Options`, the option -> `UserDefinedFlags` appliers |
| `Solver.cpp` | `Solver`: assertions, checks, budgets, interrupts, parsing, printing, statistics |
| `Model.cpp` | the detached model snapshot, the evaluator, `Model`/`ArrayValue`/`FunctionValue` |
| `Library.cpp` | `version()`, `capabilities()` |
| `c/` | the C layer (hand-written runtime + generated per-kind constructors) |

## Conventions that are not obvious from the code

- Everything public lives in `namespace stp::api`; `<stp/stp.hpp>` re-exports it into
  `stp` with a using-directive unless `STP_API_INTERNAL` is defined. The library's own
  translation units define it (Internal.h) because the engine has its own `stp::Kind`
  and `stp::UnknownReason`; inside the library write `stp::api::Kind`.
- A `Term` is a retained `ASTInternal*` plus a retained `ManagerImpl*`; the node is
  released before the manager. `NodeAccess` is the one friend of `ASTNode` that wraps
  the pointer back into a node.
- `Term::kind()` is the *public view*: the engine's `BVEXTRACT(x, hi, lo)` reads as
  `BV_EXTRACT` with one child and two indices, `NAND` as `NOT(AND)`, and so on
  (`view_of` in Terms.cpp). With `simplify = true` (the default) the manager folds
  at construction, so a term's kind is only guaranteed under `simplify = false`.
- Constant arrays are internal array symbols registered in `const_array_default`;
  every `SELECT` over them is expanded at construction (`read_const_base`), so the
  engine never sees a read of one. Equality over a constant array is UNSUPPORTED.
- Array equality is built as the engine's opaque `ARRAY_EQ` (through the factory,
  which needs `enable_array_equality`); construction switches the flag on unless the
  `array-equality` option was set to `off`.
- A model is a detached snapshot (`take_snapshot` in Model.cpp) taken at the first
  `model()` call or before the engine's tables change (`ensure_snapshot`); reading an
  arbitrary term evaluates it over the snapshot (`Evaluator`), folding through the
  simplifying factory, `NonMemberBVConstEvaluator` and `literal_fp`.
- Values of declared (uninterpreted) sorts are `ASTUninterpretedConst` nodes (an
  engine addition in this branch); they print as `S!k`.
- Options: every registry row carries an `engine` mapping (`field`, `custom` or
  `none`) in `options.toml`; `option_apply.inc` is generated from it and the custom
  appliers live in Options.cpp. Manager-scoped rows (`simplify`,
  `default-rounding-mode`, `uf-sort-width`) are refused on a solver.
- `Term::str()` (the unshared SMT-LIB form) is the API's own printer (`Smt2Printer`
  in Terms.cpp): declared names quoted only where SMT-LIB requires (non-simple
  characters, a leading digit, a reserved word), lowercase hex, `(fp ...)`
  literals, Reals in the engine's numeral spelling (`3`, `(/ 1 2)`, `(- 3)`),
  `S!k` for elements of declared sorts. A name containing `|` or `\` has no
  SMT-LIB spelling at all; it is printed quoted and does not parse back. `to_string(SMTLIB2,
  share = true)` is the engine's let-sharing printer, which quotes every symbol.
- Parsing: each `parse*` call builds a `Cpp_interface` over the manager, seeds it
  with the API's symbols (`seed_parser_symbols`), adopts the solver's pushed levels
  (`adoptAssertLevels`), keeps the functions a script declares
  (`retainUFDeclarations`), enables every theory's keywords without a set-logic
  (`all_theory_tokens`) and captures the frontend's stdout answers for the
  diagnostic of a PARSE error. CVC and SMT-LIB 1 syntax errors are recoverable
  (their `yyerror` no longer aborts; the CLI still exits with the message).
- The values of the partial floating-point operations (`fp.min`/`fp.max` on the two
  zeros, `fp.to_ubv`/`fp.to_sbv` out of range) are taken from the solve for every
  such node in the checked formula; a node built afterwards evaluates with a zero
  choice.
- CONSTANTBV's constants are thread-local, so the manager constructor boots the
  library once per thread.
- This alpha admits one live `Solver` per `TermManager` and pins a manager to the
  thread that created it. `interrupt()` reaches CaDiCaL/MiniSat mid-search through
  `UserDefinedFlags::stop_poll`; CryptoMiniSat is interrupted between solver calls.

## Engine changes made for the API

`UserDefinedFlags`: `timeout_max_time_ms`, `stop_poll`/`stop_poll_opaque`,
`random_seed`, `stop_after_cnf`. `SATSolver`: `setStopPoll`, `setSeed`.
`STPMgr`: `cnf_sink`, `CreateUninterpretedConst`. `UnknownReason::StoppedAfterCnf`.
`Cpp_interface::last_error_message`. `ASTNode` befriends `api::detail::NodeAccess`.

## The other layers

| path | contents |
|---|---|
| `include/stp/stp.h`, `c/` | the C API and its runtime (`c/NOTES.md`) |
| `bindings/python3/` | the Cython module `stp._core` and the z3py-style shell (`NOTES.md` there) |
| `lib/Compat2/` | `libstp2`: `c_interface.h` re-implemented over `stp.h` (`NOTES.md` there; `STP_LEGACY_C_INTERFACE` selects which library carries the 2.x API) |
| `tests/api/cpp3`, `tests/api/c3`, `tests/api/python3` | the suites; `FINDINGS.md` in cpp3 lists every defect met and its state |

## Building and testing

The C++ and C layers are part of `libstp`; nothing extra to enable. The Python
layer needs Cython importable by `PYTHON_EXECUTABLE` (`ENABLE_PYTHON3_API` turns
itself off otherwise). `ctest -R 'api3|c3|python3'` runs the 3.x suites;
`tests/api/cpp3/smoke.cpp` is the end-to-end check.
