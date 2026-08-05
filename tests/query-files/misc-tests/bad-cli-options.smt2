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

; RUN: not %solver --search-bias=bogus %s 2>&1 | %OutputCheck %s --check-prefix=BADBIAS
; BADBIAS-NOT: terminate called
; BADBIAS: --search-bias must be one of

; RUN: not %solver --max-time=-5 %s 2>&1 | %OutputCheck %s --check-prefix=BADTIME
; BADTIME-NOT: terminate called
; BADTIME: --max-time must be -1

; RUN: not %solver --max-num-confl=-5 %s 2>&1 | %OutputCheck %s --check-prefix=BADCONFL
; BADCONFL-NOT: terminate called
; BADCONFL: --max-num-confl must be -1

; RUN: not %solver --CVC --SMTLIB2 %s 2>&1 | %OutputCheck %s --check-prefix=BADPARSER
; BADPARSER-NOT: terminate called
; BADPARSER: more than one parsing option

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

; RUN: %solver %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; SOLVE: ^sat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= x (_ bv1 8)))
(check-sat)
(exit)
