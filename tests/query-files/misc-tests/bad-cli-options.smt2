; Bad command-line arguments must be diagnosed and exited on, never crash.
;
; lit runs RUN lines with 'set -o pipefail', so wrapping stp in 'not' checks
; the exit status even though the output is piped onwards: 'not' inverts a
; positive exit status to 0, but leaves the negative status of a process killed
; by a signal as a failure. A crash therefore fails the RUN line on its own,
; and the -NOT directives catch it a second time via the C++ runtime's message.

; --- errors detected by CLI11 --------------------------------------------

; An unrecognised option. CLI11 reports it as an unexpected argument, and
; a prefix of a real option name (--print-back) is no longer expanded to
; the full name, so it is diagnosed the same way.
; RUN: not %solver --this-option-does-not-exist %s 2>&1 | %OutputCheck %s --check-prefix=UNKNOWN
; RUN: not %solver -Z %s 2>&1 | %OutputCheck %s --check-prefix=UNKNOWN
; RUN: not %solver --print-back %s 2>&1 | %OutputCheck %s --check-prefix=UNKNOWN
; UNKNOWN-NOT: terminate called
; UNKNOWN: was not expected

; An option given without the argument it requires.
; RUN: not %solver %s --max-time 2>&1 | %OutputCheck %s --check-prefix=MISSINGARG
; MISSINGARG-NOT: terminate called
; MISSINGARG: --max-time: 1 required INT missing

; More than one input file. Only one positional argument is accepted, so
; the second file is an unexpected argument.
; RUN: not %solver %s %s 2>&1 | %OutputCheck %s --check-prefix=TOOMANY
; TOOMANY-NOT: terminate called
; TOOMANY: was not expected

; A non-boolean argument to a boolean option.
; RUN: not %solver --flattening=maybe %s 2>&1 | %OutputCheck %s --check-prefix=BADBOOL
; BADBOOL-NOT: terminate called
; BADBOOL: Could not convert

; --- errors detected by stp's own validation -----------------------------

; RUN: not %solver --cnf-generation-effort=bogus %s 2>&1 | %OutputCheck %s --check-prefix=BADEFFORT
; BADEFFORT-NOT: terminate called
; BADEFFORT: Unknown --cnf-generation-effort value

; RUN: not %solver --bv-term-abstraction-schema-groups=base,unknown %s 2>&1 | %OutputCheck %s --check-prefix=BADSCHEMAGROUP
; BADSCHEMAGROUP-NOT: terminate called
; BADSCHEMAGROUP: --bv-term-abstraction-schema-groups: unknown BV schema group 'unknown'

; RUN: not %solver --bv-term-abstraction-profile=unknown %s 2>&1 | %OutputCheck %s --check-prefix=BADBVPROFILE
; BADBVPROFILE-NOT: terminate called
; BADBVPROFILE: --bv-term-abstraction-profile: unknown BV term-abstraction profile 'unknown'

; RUN: not %solver --search-bias=bogus %s 2>&1 | %OutputCheck %s --check-prefix=BADBIAS
; BADBIAS-NOT: terminate called
; BADBIAS: --search-bias must be one of

; RUN: not %solver --incremental=bogus %s 2>&1 | %OutputCheck %s --check-prefix=BADINCREMENTAL
; BADINCREMENTAL-NOT: terminate called
; BADINCREMENTAL: --incremental must be one of

; --incremental is a flag, so a value spelled as a separate argument is read
; as the input file name instead. Diagnosed by name rather than left to fail
; later as a file that cannot be opened.
; RUN: not %solver --incremental off 2>&1 | %OutputCheck %s --check-prefix=SPLITINCREMENTAL
; SPLITINCREMENTAL-NOT: terminate called
; SPLITINCREMENTAL: --incremental takes its value attached

; RUN: not %solver --max-time=-5 %s 2>&1 | %OutputCheck %s --check-prefix=BADTIME
; BADTIME-NOT: terminate called
; BADTIME: --max-time must be -1

; RUN: not %solver --max-num-confl=-5 %s 2>&1 | %OutputCheck %s --check-prefix=BADCONFL
; BADCONFL-NOT: terminate called
; BADCONFL: --max-num-confl must be -1

; RUN: not %solver --CVC --SMTLIB2 %s 2>&1 | %OutputCheck %s --check-prefix=BADPARSER
; BADPARSER-NOT: terminate called
; BADPARSER: more than one parsing option

; --- options that cannot both take effect --------------------------------
;
; One option discarding another's is a usage error rather than a silent
; preference for whichever the code applies last. The solver flags are in
; bad-cli-options-solvers.smt2, which which solvers are compiled in decides
; whether to run at all.

; A simplification requested alongside the flag that turns the whole suite
; off. Rejected whichever way round they are given.
; RUN: not %solver --disable-simplifications --flattening=true %s 2>&1 | %OutputCheck %s --check-prefix=DISABLEDSIMP
; RUN: not %solver --flattening=true --disable-simplifications %s 2>&1 | %OutputCheck %s --check-prefix=DISABLEDSIMP
; DISABLEDSIMP-NOT: terminate called
; DISABLEDSIMP: excludes

; ... and one it agrees with: the request still had no bearing on the run.
; RUN: not %solver --disable-simplifications --disable-cbitp %s 2>&1 | %OutputCheck %s --check-prefix=DISABLEDSIMP

; --size-reducing-only likewise overrides what it forces.
; RUN: not %solver --size-reducing-only --difficulty-reversion=true %s 2>&1 | %OutputCheck %s --check-prefix=SIZEREDUCING
; SIZEREDUCING-NOT: terminate called
; SIZEREDUCING: excludes

; --bb.simplify-during-bb needs the rewriting simplifier that these turn off.
; RUN: not %solver --bb.simplify-during-bb=true --disable-opt-inc %s 2>&1 | %OutputCheck %s --check-prefix=SIMPDURINGBB
; RUN: not %solver --bb.simplify-during-bb=true --disable-simplifications %s 2>&1 | %OutputCheck %s --check-prefix=SIMPDURINGBB
; SIMPDURINGBB-NOT: terminate called
; SIMPDURINGBB: excludes

; --parse-only stops before any CNF exists to write out or exit after.
; RUN: not %solver --parse-only --output-CNF %s 2>&1 | %OutputCheck %s --check-prefix=PARSEONLY
; RUN: not %solver --parse-only --exit-after-CNF %s 2>&1 | %OutputCheck %s --check-prefix=PARSEONLY
; PARSEONLY-NOT: terminate called
; PARSEONLY: excludes

; --interactive is read only on the SMT-LIB2 path.
; RUN: not %solver --interactive=true --CVC %s 2>&1 | %OutputCheck %s --check-prefix=INTERACTIVE
; RUN: not %solver --interactive=true --SMTLIB1 %s 2>&1 | %OutputCheck %s --check-prefix=INTERACTIVE
; INTERACTIVE-NOT: terminate called
; INTERACTIVE: excludes

; --- combinations that are still accepted --------------------------------
;
; The exclusions above must not have caught anything that does take effect.

; RUN: %solver --disable-simplifications %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --flattening=true %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --size-reducing-only %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --exit-after-CNF %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --disable-simplifications --size-reducing-only %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE

; --search-bias is documented as ignored by solvers without such a setting,
; so it stays accepted next to any solver flag.
; RUN: %solver --search-bias=unsat %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE

; --- the diagnostics above go to stderr, not stdout ----------------------
;
; A caller that pipes stdout to a result parser should see nothing on a usage
; error. Checked with one representative from each of the two paths.

; RUN: not %solver --this-option-does-not-exist %s 2>/dev/null | %OutputCheck %s --check-prefix=NOSTDOUT
; RUN: not %solver --search-bias=bogus %s 2>/dev/null | %OutputCheck %s --check-prefix=NOSTDOUT
; NOSTDOUT-NOT: was not expected
; NOSTDOUT-NOT: search-bias

; --- a well-formed command line is unaffected ----------------------------

; RUN: %solver --help 2>&1 | %OutputCheck %s --check-prefix=HELP
; HELP: USAGE: stp
; HELP: --bv-term-abstraction-profile

; RUN: %solver %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; SOLVE: ^sat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= x (_ bv1 8)))
(check-sat)
(exit)
