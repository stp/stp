# Findings from the 3.x C++ API test suite

Every library defect the suite met while it was written, with its symptom,
root cause and what was done. "Fixed" entries changed the library; "open"
entries stay as they are, and the tests assert the behaviour that is there
today with a comment naming the entry.

## Fixed

### 1. `parse_smt2` line numbers were relative to the process, not the script

Symptom: the smoke test's one-line bad script reported `parse error at 5:0`
after a four-line script had been parsed earlier; a later error on line 2 of
a fresh script reported line 4. Root cause: `smt2lineno` is the flex scanner's
global line counter and nothing resets it between `SMT2ScanString` calls (the
CLI parses one file per process and never noticed). Fix: `lib/Api/Solver.cpp`
sets `smt2lineno = 1` before every scan in `run_parser` and `parse_term`.

### 2. `parse_smt2(..., ParseMode::EXECUTE)` aborted on the first `check-sat`

Symptom: `Fatal Error: Don't match` and a core dump. Root cause:
`Cpp_interface::checkSat` stops the `RunTimes::Parsing` category and restarts
it afterwards; the CLI (then `tools/stp/main_common.cpp`) started that
category before handing the file to the parser, the API did not, so the
category stack was empty when the frontend popped it. Fix: `run_parser` brackets every parse
with `start(RunTimes::Parsing)` / `stop(RunTimes::Parsing)`; the stop lives in
the restore guard, so an error path stays balanced.

### 3. `Term::to_bv_string(10)` printed a signed decimal

Symptom: `mk_bv(12, 0xabc).to_bv_string(10)` was `-1348`. Root cause: the
constant library's `BitVector_to_Dec` reads the top bit as a sign; the header
documents the string reader as the value in the given base and `to_int64` as
the signed reader. Fix: `lib/Api/Terms.cpp` renders base 10 from the bit
string (unsigned), as bases 2 and 16 already were.

### 4. `Solver::interrupt()` and a `Terminator` never stopped a running check

Symptom: an interrupt from another thread during the 96-bit factoring
instance was ignored by every backend; only a time budget ended the search.
Root cause: `Cadical::solveInternal` connects its CaDiCaL terminator only when
a deadline is set (`hasTimeLimit()`), and that terminator is the one place the
stop poll is consulted mid-search, so a stop request without a time budget was
never seen. Fix (engine, two lines): `SATSolver::hasStopPoll()` in
`include/stp/Sat/SATSolver.h` and `if (hasTimeLimit() || hasStopPoll())` in
`lib/Sat/Cadical.cpp`. CryptoMiniSat remains interruptible only between its
solver calls (`capabilities()["interrupt.cryptominisat"]`); MiniSat is not part
of this build and was not touched. The interrupt and terminator tests select
the interruptible backend and skip when the build has none.

### 5. `real_div(x, 0)` aborted inside the engine

Symptom: `Fatal Error: CreateRealTerm REAL_DIV(Real, Real): division by exact
zero`. Root cause: `build_term` only checked that the divisor is a value, and
the engine's own check is a `FatalError`. Fix: `lib/Api/Construct.cpp` refuses
a zero divisor with `UNSUPPORTED` (the kind table says the divisor must be a
non-zero value).

### 6. Printing an `FP_TO_IEEE_BV` term aborted

Symptom: `Term::str()` on `fp_to_ieee_bv(x)` died with `Fatal Error: SMTLIB2:
a float-to-IEEE-bits node (an API-only operation) has no SMT-LIB spelling`.
Root cause: the SMT-LIB 2 printer had a `FatalError` for the kind although
`kinds.toml` gives it the Z3/STP spelling `fp.to_ieee_bv`. Fix:
`lib/Printer/SMTLIBPrinter.cpp` prints `(fp.to_ieee_bv x)`.

### 7. `Model::value` on `fp.min`/`fp.max`/`fp.to_ubv`/`fp.to_sbv` aborted

Symptom: `m.value(fp_min(1.5, 2.25))` died with `FloatBlast: this partial
floating-point operation has not been totalised`. Root cause: the evaluator
collapses closed terms through the engine's constant evaluator, which blasts
floating-point nodes, and the blaster accepts the four partial kinds only in
the total form `FpTotalise` gives them at solve time (one extra child carrying
the unspecified choice); `literal_fp` deliberately skips those forms. Fix:
`Evaluator::fold` in `lib/Api/Model.cpp` appends a constant zero choice child,
so every specified case folds through the engine and the unspecified ones
(`min(+0, -0)`, a conversion of NaN, an infinity or an out-of-range value)
evaluate to that choice instead of aborting.

### 8. A manager-scoped `anytime` row set on a live solver was stored before it was refused

Symptom: `s.options().set_str("default-rounding-mode", "RTZ")` threw
`OPTION_VALUE` from the applier but `get_str` then read `RTZ`. Root cause:
`SolverOptions` wrote the value into the live store before `apply_one` ran the
refusing applier. Fix: `live_write` in `lib/Api/Solver.cpp` refuses
manager-scoped rows before anything is stored.

### 9. `Options::set_args` was not all-or-nothing

Symptom: `o.set_args({"--flattening=true", "--nope"})` threw `OPTION_UNKNOWN`
and left `flattening` changed. Root cause: the entries were applied one by one
into the live store (the `SolverOptions` overload already parsed into a copy).
Fix: `Options::set_args` in `lib/Api/Options.cpp` parses into a copy and
swaps it in.

### 10. `options.toml`: `stop-after-cnf` was mapped onto the engine's `exit_after_CNF`

The row's `engine` field named `exit_after_CNF`, the 2.x flag that calls
`exit(0)` inside the library after the first CNF, although the row's help text
and `UnknownReason::STOPPED_AFTER_CNF` describe the branch's new
`stop_after_cnf` flag (which abandons the check with `unknown`). Setting the
option through the API would have terminated the process. The row now reads
`engine = { field = "stop_after_cnf" }`; `api3-solver.cpp` checks the option
answers `unknown (stopped-after-cnf)`.

### 12. A refused `Solver` construction left the manager with a dangling live solver

Symptom: after `Solver(tm, o)` threw `OPTION_UNAVAILABLE` (a backend the
build lacks) or `OPTION_VALUE` (a manager-scoped row), every later `Solver(tm)`
was refused with `UNSUPPORTED` ("one live solver per manager"). Root cause:
`SolverImpl`'s constructor registered itself as the manager's live solver and
pushed the base level before applying the options, and a throwing constructor
runs no destructor, so the registration, the engine and the manager's
reference count all leaked. Fix: the constructor undoes all of that in a
catch-and-rethrow.

### 13. `Solver::assertions()` collapsed to one formula per level after an incremental check

Symptom: three assertions, a `push`, a check, then `assertions().size() == 1`.
Root cause: the incremental branch of `run_check` used the engine's
`getVectorOfAsserts()`, which rewrites every level into its conjunction (and
fills empty levels with `true`) as a side effect. Fix: the level vector is
built from `AssertLevels()` without touching them. The frontend's own
`check-sat` (a script's, in either parse mode) still runs
`getVectorOfAsserts()`, so a script containing `(check-sat)` leaves each
level as one conjunction; recorded under the known differences below.

### 14. A script could not pop a level pushed by the API or by an earlier script

Symptom: `s.push(); s.parse_smt2("(assert ...)(pop 1)")` died with `Fatal
Error: Can't pop away the default base element`. Root cause: `run_parser`
constructs a fresh `Cpp_interface` per call, whose frame stack starts at one
frame while the manager's assertion stack is deeper. Fix:
`Cpp_interface::adoptAssertLevels()` (new, `lib/Interface/cpp_interface.cpp`)
adds a frame and a cache entry per existing level, called after construction
in `run_parser` and `parse_term`.

### 15. `Model::value` aborted on `distinct`, on Real orderings and on declared-sort equality

Symptom: `Fatal Error: BVConstEvaluator: The input kind is not supported yet`
for `distinct(...)` over values, for `real_lt`/`real_le`/`real_gt`/`real_ge`
over Real values (the engine folds Real arithmetic at construction but not the
orderings) and for `=` over elements of a declared sort. Fix in
`lib/Api/Model.cpp`: the evaluator answers `DISTINCT` pairwise on the
evaluated operands, compares Real values exactly with decimal big-integer
arithmetic (the engine's `ExactRational` needs a number-budget scope), and
compares declared-sort values by identity. It also reads a term the exact
Real model valued as a whole (its `scalars`) before descending into it.

### 16. Unused functions were in the model core; `in_core` disagreed with `symbols()`

Symptom: `m.symbols()` listed a declared but never applied function, and
`in_core(f)` was true for it. Root cause: the vacuous default seed gives every
active declaration a table, and `in_core` looked the tables up rather than the
core. Fix: only functions with at least one case join the core, `in_core` is
membership of the core, and the Real model's application values no longer
count as core symbols.

### 17. A function symbol printed as its engine identity

Symptom: `std::cout << f` printed `|@uf_decl_0|` while `f.symbol()` was `f`.
Fix: `print_term` in `lib/Api/Terms.cpp` prints a declared function's name.

### 18. `mk_fp(sort, rm, "-0.0")` was the positive zero

Root cause: the decimal and rational converters lose the sign of zero (the
double overload special-cased it). Fix in `lib/Api/Manager.cpp`: a negative
zero literal in either text form is the negative zero.

### 19. `parse_term` could not parse a Boolean text

Symptom: `parse_term("(bvult px py)")` raised `PARSE` ("Must be >=2
operands"). Root cause: the implementation parsed `(assert (= t t))` and took
the first operand; for a Boolean `t` the hashing factory makes one operand of
the two identical formulas and the grammar's `createNode` refuses a
one-operand node. Fix in `lib/Api/Solver.cpp`: a Boolean text is asserted as
it stands on the scratch level (a speculative first attempt whose frontend
echo is kept off stdout), and every other sort goes through the
self-equality as before.

### 20. A failed `parse_smt2` kept what the script had asserted and pushed

Symptom: after `parse_smt2("(assert (= a #x01)")` raised `PARSE` (missing
parenthesis) the assertion was on the stack, and a script that pushed and then
failed left its level behind. Root cause: the frontend's `assert` and `push`
actions fire as the commands are reduced, before the error. Fix in
`run_parser`: the stack's shape (level count, size of every level) is recorded
before the parse and restored before the failure is reported.

### 21. `Solver::to_smt2` omitted the `declare-fun` of a function symbol

Symptom: the text of a problem with `f(x)` had no declaration of `f` and did
not parse back. Root cause: a function's identity node is one of the engine's
introduced symbols, which the printer skips. Fix: the skip spares nodes that
carry a function declaration.

### 22. `TermManager::simplify` left an unfolded node alone

Symptom: `simplify(parse_term("(bvult px py)"))` was not the manager's own
`bvult(px, py)` (spelled `bvugt`): the rebuild only re-folded a node whose
children had changed, so a node built without folding stayed as it was. Fix in
`lib/Api/Manager.cpp`: every node goes through the folding factory (a hash
lookup when nothing applies).

### 23. `smt2.y`: two `exit(1)` calls in the grammar's node builders

`createNode` and `createTerm` refused a one-operand n-ary node by calling
`yyerror` and then `exit(1)`, so `parse_term("")` (and any `(bvadd x)`)
terminated the process. Both now unwind with `stp::DeclassifiedNameAbandon`,
which `SMT2Parse()` already turns into a failed parse.

### 24. A function a script declared was lost when the script ended

Symptom: after `parse_smt2("(set-logic QF_AUFBV) (declare-fun f ((_ BitVec 8))
(_ BitVec 8)) ... (assert (= (f x) y))")`, `tm.symbol("f")` was empty and
`check_sat()` died with `Fatal Error: SimplifyTerm: Control should never reach
here: (UF_APPLY @uf_decl_0 ...)`, while the same problem built through the API
was sat. Three causes, one behind the other: (i) `adopt_engine_symbols`
skipped the function's identity node before asking whether it carries a
declaration, because that node is one of the engine's introduced symbols and
its name `@uf_decl_N` is reserved; (ii) the SMT-LIB 2 grammar calls
`Cpp_interface::cleanUp()` when the script ends (`cmd: commands END`), which
destroys the frontend's frames, and a frame deactivates the functions declared
in it -- right for a `(pop)`, and for the CLI, whose interface lives as long
as the manager, but here the manager and the terms applying the function live
on; (iii) the same teardown puts back the `enable_uninterpreted_functions` and
`enable_array_equality` switches that the script's `set-logic` turned on, so
re-enabling them while the interface was alive was undone. Fix: adoption looks
the declaration up first (`lib/Api/Manager.cpp`);
`Cpp_interface::retainUFDeclarations(bool)` (new,
`lib/Interface/cpp_interface.cpp`) makes `cleanUp` release the frames'
declarations instead of deactivating them, and `run_parser` turns it on for
the parse and off again for a failed script; and the switches are decided
after the frontend is gone -- on when declarations are active, or when an
array equality was parsed.

### 25. A script needed `set-logic` (or the 2.x switches) to declare a function, apply one or compare arrays

Symptom: `parse_smt2("(declare-fun f ((_ BitVec 8)) (_ BitVec 8)) ...")`
without a `set-logic` naming UF raised `PARSE` ("unexpected LPAREN_TOK,
expecting RPAREN_TOK"), and `(assert (= a b))` over arrays without an array
logic aborted in `HashingNodeFactory` ("STP cannot decide equality between
whole array terms without --array-equality"). Root cause: the grammar admits
the UF syntax only while `enable_uninterpreted_functions` is on and the
factory builds an array equality only while `enable_array_equality` is, which
the CLI has `set-logic`, `-u` and `-x` turn on; the API's own construction
turns them on itself. Fix: `run_parser` turns both on for the duration of the
parse and decides their values afterwards (24).

### 26. Content a forced-off theory switch cannot decide aborted the engine

Symptom: with `uninterpreted-functions = off` and an application asserted
(built or parsed), `check_sat` died in `SimplifyTerm` (`UF_APPLY` reached the
simplifier), and `f(x)` built after such a check raised `INVALID_ARGUMENT`
("uninterpreted functions are disabled"); with `array-equality = off` set
after an array equality was asserted (the row is `before-first-check`, so
this is legal) `check_sat` died in `TransformFormula`; a parsed `(= a b)`
under `array-equality = off` aborted at construction. Fix: `run_check`
refuses both with `UNSUPPORTED` before anything changes (the refused check is
no check, so the mode can still be changed); `run_parser` refuses a script
comparing arrays under `array-equality = off` with `UNSUPPORTED`, the stack
put back and the script's function declarations deactivated; and the API's
`apply` turns the engine's switch on as `declare` already did, since the
design has applications always constructible.

### 27. `auto` after `off` did not re-engage the machinery

Symptom: `set("uninterpreted-functions", "off")`, a refused check,
`set(..., "auto")`, then `check_sat` was still refused: `auto` left the engine
switch as it was, relying on `declare`'s side effect, which `off` had undone.
The same for `array-equality`. Fix in `lib/Api/Options.cpp`: `auto` derives
the switch from the content at every apply -- the active declarations for UF,
and a new `ManagerImpl::array_equality_seen` (set when an array equality is
built or parsed) for arrays.

### 28. Parsing without `set-logic` could not read `(_ BitVec 8)`

Symptom: once 25's fix opened every theory's tokens for an API parse
(`all_theory_tokens`), `parse_smt2("(declare-fun x () (_ BitVec 8)) ...")`
raised `PARSE` ("unexpected REAL_NUMERAL_TOK, expecting NUMERAL_TOK token:
8"). Root cause: with the Real gate open the lexer hands every numeral back as
a Real literal, which is right in a QF_LRA script (no indexed identifier
occurs there) and wrong for an index or a width. Fix: the lexer tracks whether
it is inside an indexed identifier (`(_` up to its `)`), where a numeral is
always an index, and returns `NUMERAL_TOK` there whatever the gate says; and a
`(reset)` inside a script restores the gates the caller opened instead of
closing them. Found by the integrated build, the first to run the c3, api3 and
python3 suites against a tree carrying both changes.

### 11. `options.toml`: the `--SMTLIB1` frontend row lacked its `-m` short flag

Found by `lib/Api/gen/check_cli_parity.py` (CTest `api3-cli-parity`):
`tools/stp/main.cpp` registers `"--SMTLIB1,-m"`, the `[[frontend]]` row said
`--CVC | --SMTLIB1 | --SMTLIB2`. The row now reads
`--CVC | --SMTLIB1, -m | --SMTLIB2`. The check also lists the eight registry
spellings with no CLI form (`--produce-models`, `--sat-backend`,
`--random-seed`, `--model-array-fill`, `--logic`, `--simplify`,
`--default-rounding-mode`, `--stop-after-cnf`), which are new in 3.x.

Superseded: `tools/stp/main.cpp` now registers its command line from
`options.toml` itself (every entry with a `cli_form`, the `[[alias]]` backend
flags and the `[[frontend]]` rows), so there are no two copies to compare.
`check_cli_parity.py` is gone; `api3-registry` holds the registry's defaults
to the engine's and the CLI tables to the entries, and `api3-cli-help` reads
the built binary's `--help` back against the table. Six of the eight spellings
above are on the command line now (`--model-array-fill` and
`--default-rounding-mode` are API-only, `cli_form = "none"`).

### 29. The frontend's refusals ended the process (A and F)

Symptom: a sort error inside a script (`(= x #b1)` over an 8-bit `x`, a
Boolean where a bit-vector was expected, an ill-formatted float operation),
a wrong arity or argument sort of a declared function, a redeclaration, an
unsupported function sort, an invalid declaration name, `fp.to_real`, the
one-argument `to_fp` of a literal, a Boolean option given `maybe`,
`:global-declarations` set after a declaration, a sort name defined twice, a
reserved `@` name, a `(pop)` with nothing pushed, a zero width, too few
operands, and `(_ bv300 8)` all reached `FatalError` from `fatal_yyerror`,
`Cpp_interface::refuseCurrentCommand`, `badBooleanOptionValue`, the four
frontend sites named, or the engine's constant constructor, and the process
ended. Fix, in the engine: each reports as before and then throws
`ParseAbandon` (the base of `DeclassifiedNameAbandon`) to `SMT2Parse()`, which
answers failure, so the parse ends as a whole and no later command runs; the
command line is unchanged (the `(error ...)` response, the "Fatal Error:"
line on stderr, and the registered handler, whose `exit(-1)` ends the run
with status 255 as it always did), and its lit tests pass unchanged. The
`(_ bvN w)` rule checks that N fits w bits before the constructor sees it.
Under the API the parse comes back as `PARSE` with the stack put back, as a
syntax error always did. A command the frontend answers with `(error ...)`
and then skips (an ill-typed `extract`) used to leave the parse "successful"
with the assertion silently dropped: for the API that is a failed parse too.
The engine's death test pinning the abort
(`UninterpretedFunctionsFrontend.MalformedParserApplicationRefusesTheWholeCommand`)
pins the new contract: failure, the diagnostic on every channel, nothing on
the assertion stack. `Parsing.function_misuse_in_a_script_is_a_parse_error`
is enabled and `Parsing.frontend_refusals_are_parse_errors` covers the list.

### 30. An engine `FatalError` under the API ended the process

Symptom: an engine invariant reached through any API call (`Term::to_string`
of a Real term in the CVC format, say) called `FatalError`, which
`abort()`ed. Fix: `FatalError` throws `stp::EngineFatal` while the thread's
`FatalErrorThrows()` flag is set (else it ends the process as before: code
that drives the engine directly never sets it, and the stp binary and libstp2
now reach the engine through the API). The API sets it around
every engine-reaching entry (`EngineScope`/`engine_call` in `Internal.h`:
construction, `simplify`, declare, the solver's construction, assert, push,
pop, checks, parses, models, printing, options) and turns the exception into
`INTERNAL`, poisoning the manager: every later call on it, its solvers,
models and terms is `STATE` naming the failure. The C and Python layers
inherit it (the C boundary also nets an `EngineFatal` no hub converted).
The CVC printer's gaps (a float, a Real, an application) are refused as
`UNSUPPORTED` before the printer, in `Term::to_string` and
`Solver::to_string`; after that no public entry reaches a `FatalError` with
valid input, so `api3-engine-failure.cpp` exercises the seam through the
internal header.

### 31. `options.toml` had drifted from the command line it described

Found when `tools/stp/main.cpp` began registering its options from the table
and the lit suite ran against the result. Four `follows = "bb.fp-native-all"`
relations were wrong: only the nine per-operation circuits (`arith`, `minmax`,
`pack`, `round`, `sqrt`, `fma`, `conv`, `rem`, `div`) took the all-switch's
value on the CLI; `bb.fp-native-cmp`, `bb.fp-native-add-iszero`,
`bb.fp-native-domain` and `bb.fp-native-known-sign` never did, and with the
relation `--bb.fp-native-all=false` switched them off too (six
`fp-tests/native-*` cases changed their SymFPU operation counts). The three
CaDiCaL knobs (`cadical-elim`, `-elimmineff`, `-elimmaxeff`) use `-1` as the
API's "unset" sentinel, which the CLI never accepted (`tests/cadical_options.py`
requires `--cadical-elim=-1` to fail); the rows now carry a `cli_range` the
binary checks itself. And five refusal wordings the tests pin
(`Unknown --cnf-generation-effort value 'x'. Expected one of: ...`,
`--fp-abstraction-ops: unknown operation in 'x'`, `unknown BV schema group
'x'`, `unknown BV term-abstraction profile 'x'`, the `mode_arg` rows'
`expected auto, on/1/true, or off/0/false`) differ from the registry's generic
message; the rows spell them out as `cli_bad_value` templates. `exit-after-CNF`
is a `[[frontend]]` row rather than an alias of `stop-after-cnf`: 2.x's flag
exits the process where the 3.x entry answers unknown. The list the
`cnf-generation-effort` refusal printed omitted `new-high`, an accepted
value; the template and the lit test that pins it now name it. A row's
template words only the registry's own refusal of a value or member: the
schema-group row's applier (the engine's parser) keeps its own wording
("'all' and 'none' must be used alone"), and the row's `{expected}` hole
lists the groups as the engine does.

## Open

### A. A sort error inside a parsed script still aborts (FIXED, see 29)

`fatal_yyerror` in `lib/Parser/smt2.y` (for example "bitvector operator
requires bitvector operands", "expected a rounding mode") calls
`stp::FatalError`, which `abort()`s, so `Solver::parse_smt2` cannot turn every
malformed script into a `PARSE` error; a syntax error (bison's `yyerror`), an
undeclared symbol are reported correctly; the five refusals of F are as
fatal. The parse tests stay on the recoverable path. An engine change (throwing from
`fatal_yyerror`, and from `Cpp_interface::badBooleanOptionValue`) is needed.

### B. A second live solver cannot be constructed after a refused one (FIXED, see 12)

### C. Two managers on two threads corrupt the heap (FIXED: CONSTANTBV is booted per thread)

With a manager, a solver and a model live on the main thread, a second
thread that creates its own manager, declares a symbol and asserts an
equality corrupts the heap inside the engine (`STPMgr::LookupOrCreateBVConst`
allocating in the new thread's arena; glibc reports
`malloc(): invalid size (unsorted)`, mimalloc segfaults in
`_mi_page_malloc_zero`). The same work on a thread that is the only user of
the engine in the process succeeds, and so does the same sequence on one
thread. Every API entry the second thread makes on the first manager is
refused with `STATE` as designed, so this is engine state shared between
`STPMgr` instances, not the API's pinning. Reproducer: `Threads.a_manager_created_on_another_thread_works_there` in
`api3-errors.cpp` (enabled since the fix). The pin itself is gone too: a
manager may be used from any thread, one call at a time (node ids are
process-wide, the constant library boots per thread at every entry point),
and any number of solvers may be live over one manager (`api3-solvers.cpp`).

### D. A CVC or SMT-LIB 1 syntax error aborts, and CVC input requires a `QUERY`

`yyerror` in `lib/Parser/cvc.y` and in `lib/Parser/smt.y` prints the
diagnostic and calls `FatalError`, so `Solver::parse(text, Format::CVC)` and
`parse(text, Format::SMTLIB1)` cannot report a `PARSE` error for malformed
input (the SMT-LIB 2 grammar reports a syntax error recoverably). The grammar's `other_cmd` always ends in a `Query`,
so a CVC text with declarations and assertions but no `QUERY` is itself a
syntax error (and an abort). The tests spell "only assertions" as
`QUERY(FALSE);`, which `run_parser` recognises: its negation folds to `true`
and is not asserted. The CVC and SMT-LIB 1 scanners' line counters are as
cumulative as the SMT-LIB 2 one was, but their errors never reach an
exception, so nothing reads them.

### E. `Cpp_interface::error` echoes `(error "...")` to stdout

A parse error that becomes a `PARSE` exception is also printed on stdout by
the frontend, which the header's "nothing prints on its own" excludes. The
tests capture stdout around the calls that provoke it.

### F. Five script errors end the process instead of the parse (FIXED, see 29)

`Cpp_interface::refuseCurrentCommand` -- reached by redeclaring a function,
applying one to the wrong number or sort of arguments, an unsupported UF
sort and an invalid top-level declaration name -- reports the diagnostic and
calls `FatalError`, so `parse_smt2` of such a script aborts instead of
raising `PARSE`. The frontend does this on purpose: recovering from a
malformed application once dropped the assertion it sat in and let the
script's next `check-sat` answer a weaker query (the comment on
`UninterpretedFunctionsFrontend.MalformedParserApplicationRefusesTheWholeCommand`,
a death test that pins the abort). Unwinding to `SMT2Parse()` with
`DeclassifiedNameAbandon` instead of aborting was tried here and works for
both callers -- the parse fails as a whole, so no later command of that script
runs; the CLI prints the diagnostic and exits non-zero through its
failed-parse path (now `tools/stp/run.cpp`), and the API reports `PARSE`
with its solver put back -- but it fails that death test, so it was not
kept. `Parsing.DISABLED_function_misuse_in_a_script_is_a_parse_error` holds
the expectations for when the frontend's refusal ends the parse rather than
the process.

## Known differences from the intended behaviour (recorded, not changed)

- **Construction-time lowering survives `simplify = false`.** `kind()`
  reports the lowered form for `BV_NAND`/`BV_NOR`/`BV_XNOR` (`BV_NOT` over the
  bitwise op), `BV_REPEAT` and `BV_ROTATE_*` (`BV_CONCAT`, or the operand
  itself for a full rotation or `repeat 1`), `BV_COMP`, `BV_REDAND`,
  `BV_REDOR` (`ITE` over an equality), `BV_NEGO` (`EQUAL`), `BV_SDIVO`
  (`AND`), `FP_FP` (`FP_TO_FP_FROM_BV` over a concat), an n-ary `BV_CONCAT`
  (a chain of binary ones), `BV_ZERO_EXTEND`/`BV_SIGN_EXTEND` by 0 (the
  operand), `AND`/`OR` of one argument (the argument), and `DISTINCT` over FP,
  Real or array sorts (`NOT` of the equality, or an `AND` of those).
  `kinds.toml` lists these as `folds`, which its header defines as the rewrites
  applied when `simplify = true`, and the API means to keep structure
  faithful under `simplify = false`. The engine has no node kinds for most of them, so
  `api3-kinds.cpp` asserts the lowered view (the lines marked `lowered:`).
- **Array equality against a constant array was `UNSUPPORTED`** (FIXED
  2026-09-27: constant arrays are the engine's, with the extensionality
  checker's rules K and K' and the completed models; `api3-const-arrays.cpp`),
  so `ArrayValue::as_term()` can be re-asserted as `a == av.as_term()` and the
  Rosetta R4 program states `b == c` directly. `Model::value` of an
  array-sorted term returns the term itself rather than a store chain over a
  constant array; `array_value()` is the data door.
- **`sat-backend` naming a backend the build lacks is refused at solver
  construction**, not "at set time" as the registry's help text says:
  `Options::set_str("sat-backend", "minisat")` succeeds on a build without
  MiniSat and `Solver(tm, o)` raises `OPTION_UNAVAILABLE`.
- **`--no-<name>` is accepted for every bool option** by `set_args`, not only
  for the entry that declares a `negation` (`incremental-promote-units`).
- **`check-sat` executed by `ParseMode::EXECUTE`** answers inside the frontend
  (its verdict prints only under the frontend-only `-n` flag; `(get-model)`
  and `(get-value ...)` print) and is not reflected in `Solver::model()` or
  `unsat_assumptions()`; the next API check starts afresh.
- **`unsat_assumptions()` after a batch (non-incremental) check** returns every
  assumption, not the failed subset; the subset is reported when the
  incremental driver ran the check (`incremental = on`, or auto-engaged).
- **A function over Reals is tabled from the exact model.** The certified UF
  seed carries bit-level values only, so the snapshot records the value of
  each application of such a function in the checked formula (the exact
  model's, for a Real result) and tables it by its arguments' values; an
  application the check never saw completes to the codomain's default. A Real
  argument with a bit-vector result under a comparison is refused by the
  engine at assertion (`UNSUPPORTED`).
- **The literal FP converters need at least 3 exponent bits**: `mk_fp(sort,
  rm, double)` and the text form raise `UNSUPPORTED` for `(_ FloatingPoint 2
  s)`; `mk_fp_from_bits` still builds those values.
- **`stop-after-cnf` stops the batch pipeline only**: a session the pushes
  made incremental answers the check instead.
- **`excludes` are checked whenever both entries are set**, whatever their
  values: `switch-word = true` with `disable-simplifications = false` is an
  `OPTION_CONFLICT`.
- **A function a script declares is the manager's**, like a declared constant
  (the manager's name table is unscoped): it survives an API `pop()` of the
  level it was declared in. A `(pop)` inside the script does deactivate it (the
  frontend's own scoping), and it is then not adopted. A script's
  `(check-sat)`, in either parse mode, still leaves each level as one
  conjunction (13).
