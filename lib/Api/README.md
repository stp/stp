# The STP 3.x API (alpha)

This directory implements the STP 3.x API: `<stp/stp.hpp>` is the primary, C++17 surface; `<stp/stp.h>`
is the C layer over it; `stp._core` (Cython) is the Python layer over the C layer;
`libstp2` re-implements the 2.x `c_interface.h` over `stp.h`.

## Layout

| path | contents |
|---|---|
| `tables/*.toml` | the single-source tables: kinds (102), options (238), errors (21), statistics (63) |
| `gen/generate.py` | writes every generated fragment into `<build>/generated/` (C++ and C enums, named constructors, registry rows, Cython enums) |
| `Internal.h` | the private structures: `ManagerImpl`, `SolverImpl`, `ModelSnapshot`, `OptionsImpl` |
| `Registry.h` | the option registry's rows (`OptionSpec`) and the command line's rows, which the `stp` binary reads too |
| `Errors.cpp` | exception classes, throw helpers, enum spellings |
| `Manager.cpp` | `TermManager`, `Sort`, sorts/symbols/literal values over `STPMgr` |
| `Terms.cpp` | `Term`: the public view of an engine node, typed readers, printing, substitution |
| `Construct.cpp` | `build_term`: type checking for every kind and its mapping onto engine nodes; named constructors, literal helpers, operators |
| `Options.cpp` | the registry, `Options`, the option -> `UserDefinedFlags` appliers |
| `Solver.cpp` | `Solver`: assertions, checks, budgets, interrupts, parsing, printing, statistics |
| `Model.cpp` | the detached model snapshot, the evaluator, `Model`/`ArrayValue`/`FunctionValue` |
| `Library.cpp` | `version()`, `capabilities()` |
| `Output.cpp` | where the engine's `std::cout` and `std::cerr` text goes while it works for a solver (`OutputRoute`) |
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
  The switch picks the factory the API's construction and the parsers use
  (`ManagerImpl::factory`); the engine's own `defaultNodeFactory` folds either way.
- Constant arrays are the engine's: `STPMgr::CreateConstArray` registers an
  introduced array symbol with its default, interned by sort and default, so a
  script's `((as const S) v)` and `mk_const_array` give one term. The default is
  a value (`STPMgr::firstFreeSymbol` finds no symbol in it): the registry is out
  of the preprocessing passes' sight, so a variable in a default could be
  eliminated while the array still named it. The hashing
  factory folds every read of one to the default in both construction modes, and
  the extensionality checker decides equality, distinct, ite and store chains
  over them (rules K and K' in `lib/Extensionality/ExtChecker.cpp`), completing
  an array it equates with a constant array with that default; the model printers
  and `Model::array_value` take the completion from the engine. The API asks
  `is_const_array` / `const_array_default` on the manager.
- `fp.to_real` is the engine's (`STPMgr::CreateFpToReal`, lib/STPManager/FpToReal.cpp),
  shared with the SMT-LIB 2 frontend: a float value folds to its exact Real value;
  a symbolic float is an exact linear encoding over its bits, the exponent applied
  one bit at a time with constant factors, so the term has `eb + sb + 3`
  if-then-elses whatever the format. NaN, +oo and -oo of each format select a Real
  constant of their own. The encoding's root names the operand
  (`FpToRealOperand`), which is how `kind()`, `simplify`, `substitute`, the model
  evaluator and the printers treat it as `(fp.to_real x)`. At solve time
  `LinkFpToReal` adds, for each comparison of a conversion against a constant or
  against a conversion of the same format, the floating-point comparison it is
  for finite operands, so the SAT search sees it while choosing the bits.
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
- The `stp` binary is a client of this API: `tools/stp/main.cpp` registers
  every row with a `cli_form` (value, flag or none) from its OptionSpec, the
  `[[alias]]` backend flags and the `[[frontend]]` rows (`cli_table.inc`, read
  through `Registry.h`), hands each value to `stp::Options` as text and makes
  the solver from them; `tools/stp/run.cpp` reads the input with
  `Solver::parse(std::istream&, Format, ParseMode::EXECUTE)` (or `PARSE_ONLY`)
  and puts the sinks' text on stdout and stderr. The `--help` groups come from
  the `[[cli_group]]` and `[[category]]` sections; `option_defaults.inc` lets
  `registry` hold the table's defaults to `UserDefinedFlags`, and
  `cli-help` reads the built binary's `--help` back against the table.
  What stays hand-written in main.cpp is listed in its header comment.
- `Term::str()` (the unshared SMT-LIB form) is the API's own printer (`Smt2Printer`
  in Terms.cpp): declared names quoted only where SMT-LIB requires (non-simple
  characters, a leading digit, a reserved word), lowercase hex, `(fp ...)`
  literals, Reals in the engine's numeral spelling (`3`, `(/ 1 2)`, `(- 3)`),
  `S!k` for elements of declared sorts. A name containing `|` or `\` has no
  SMT-LIB spelling at all; it is printed quoted and does not parse back. `to_string(SMTLIB2,
  share = true)` is the engine's let-sharing printer, which quotes every symbol.
- Parsing: each `parse*` call builds a `Cpp_interface` over the manager's
  factory behind a `TypeChecker`, seeds it with the API's symbols
  (`seed_parser_symbols`), adopts the solver's pushed levels
  (`adoptAssertLevels`) and keeps the functions a script declares
  (`retainUFDeclarations`). Under `DECLARE_AND_ASSERT` it enables every
  theory's keywords without a set-logic (`all_theory_tokens`) and captures the
  frontend's stdout answers for the diagnostic of a PARSE error; `EXECUTE` and
  `PARSE_ONLY` read the input as the command line does, under the script's own
  set-logic, answering to the output sink, and a CVC or SMT-LIB 1 query is
  decided there as `TopLevelSTP(assertions, query)` and answered by
  `PrintOutput`. A stream is read through the lexers' reader hook
  (`setSMT2Reader` and its twins in parser.h), one refill at a time. CVC and
  SMT-LIB 1 syntax errors are recoverable (their `yyerror` no longer aborts;
  the CLI still exits with the message). The
  SMT-LIB 2 frontend's own refusals (a sort error, a wrong arity, a
  redeclaration, a constant that does not fit its width, an option value it
  cannot read) unwind to the parse entry with `ParseAbandon` and are PARSE
  errors with the stack put back; a command the frontend answers with
  `(error ...)` and then skips makes the parse fail too, since STP's error
  behaviour is immediate-exit and a silently dropped assertion is worse than
  a refused script (under `DECLARE_AND_ASSERT`; a run answers it and goes on,
  as the command line does). Every channel keeps its report: the response, the
  "Fatal Error:" line on the diagnostic sink and the fatal error handler.
- Errors: the library never calls `exit()` or `abort()`. A misuse is a
  recoverable error that leaves every object as it was. An engine failure --
  `FatalError` reached inside any API call -- throws `stp::EngineFatal`
  because every engine-reaching entry runs inside an `EngineScope`
  (`engine_call` in Internal.h); the hub reports it as INTERNAL and poisons the
  manager, whose state the failure may have left inconsistent: every later
  call on it, its solvers, models and terms is refused with STATE naming the
  failure. Any other exception that unwinds through the engine (a
  `std::exception` it or a caller's callback threw) is such a failure too
  (`fail_foreign`): INTERNAL, or RESOURCE for `std::bad_alloc`, and the
  manager is poisoned. `FatalError` and `ReportFatalError` tell the engine's per-thread
  observer first, which a solver's route points at its fatal error handler:
  the `stp` binary prints "STP Error:" there and exits, before anything
  unwinds, as it always did. libstp2, the 2.x C interface over the C API,
  reports such a failure through the 2.x error handler and then aborts, as 2.x
  did, unless `vc_setErrorPolicy` asked for `STP_ON_ERROR_RETURN`.
- Output: the engine prints with `std::cout` and `std::cerr`. The first route
  (`OutputRoute`, Output.cpp) puts a dispatching buffer in front of each
  stream's own; while a route is alive on a thread, that thread's writes go to
  the route's sinks (a solver's output and diagnostic sinks) or nowhere, and a
  flush of `std::cout` reaches the output sink as an empty chunk. A solver's
  entries route to its own sinks; `engine_call` routes everything else nowhere.
  A thread with no route writes to the process's streams as before. What a SAT
  library prints with C stdio (CaDiCaL's and MiniSat's verbose reports, which
  `stats_flag` switches on) bypasses the streams and so the routes.
- The values of the partial floating-point operations (`fp.min`/`fp.max` on the two
  zeros, `fp.to_ubv`/`fp.to_sbv` out of range) are taken from the solve for every
  such node in the checked formula; a node built afterwards evaluates with a zero
  choice.
- CONSTANTBV's constants are thread-local, so every entry point boots the library
  on the calling thread (one thread-local read once a thread has booted), and
  node ids come from one process-wide atomic counter. A manager and everything
  created from it may be used from any thread, one call at a time (the caller
  serialises); `Solver::interrupt()` may be called from any thread at any time.
- Any number of `Solver`s may be live over one `TermManager`. The engine has one
  assertion stack and one set of flags per manager, so each solver mirrors its
  levels: the solver in use (the active one) owns the engine's stack and flags,
  and a switch shelves the previous solver's levels (its pending model is
  snapshotted first), installs the new one's, and re-applies its options over
  every registry default (`SolverImpl::activate`). The incremental driver is each
  solver's own and is handed its levels afresh at every check, so it is not
  affected. The cost is the replay of the stack at every switch: alternating two
  solvers with large stacks pays it every time. The engine's coverage counters
  (`statistics()` entries other than the per-solver ones) are per manager.
- `interrupt()` reaches CaDiCaL/MiniSat mid-search through
  `UserDefinedFlags::stop_poll`; CryptoMiniSat is interrupted between solver calls.

## Engine changes made for the API

`UserDefinedFlags`: `timeout_max_time_ms`, `stop_poll`/`stop_poll_opaque`,
`random_seed`, `stop_after_cnf`. `SATSolver`: `setStopPoll`, `setSeed`.
`STPMgr`: `cnf_sink`, `CreateUninterpretedConst`. `UnknownReason::StoppedAfterCnf`.
`Cpp_interface`: `last_error_message`, and `getDeclaredSymbols` with
`keepDeclaredSymbolsAtCleanup` (what a script declared outlives its frames).
`ASTNode` befriends `api::detail::NodeAccess`.
For running an input as the command line does: a lexer reads through a
`ParserReader` when one is set (`setSMT2Reader`, `setCVCReader`,
`setSMTReader`); `SetFatalErrorObserver` tells a per-thread observer of every
fatal error before anything unwinds; `STPMgr::cnf_listener` receives every CNF
with its `CnfExtent`; and `exit_after_CNF` ends the run rather than the
process (`STPMgr::run_ended_after_cnf`, and `ScriptEnded` in the SMT-LIB 2
frontend).

## The other layers

| path | contents |
|---|---|
| `include/stp/stp.h`, `c/` | the C API and its runtime (`c/NOTES.md`) |
| `bindings/python/` | the Cython module `stp._core` and the z3py-style shell (`NOTES.md` there) |
| `lib/Compat2/` | `libstp2`: `c_interface.h` re-implemented over `stp.h`, the only provider of the 2.x API (`NOTES.md` there) |
| `tests/api/cpp`, `tests/api/c`, `tests/api/python` | the suites; the limits they pin are listed in `docs/api.rst` |

## Building and testing

The C++ and C layers are part of `libstp`; nothing extra to enable. The Python
layer needs Cython importable by `PYTHON_EXECUTABLE` (`ENABLE_PYTHON_API` turns
itself off otherwise). `ctest -L api` runs the suites, `libstp2`'s (labelled
`api2`) with them; `tests/api/cpp/smoke.cpp` is the end-to-end check.
