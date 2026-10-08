; The SAT search reset needs a backend that can do one.
;
; tools/stp refuses the pair before it reads the input. A script's set-option
; and the API reach neither that check nor run_check_impl, so the setting went
; through to LraCoordinator, whose refusal arrives as an exception the engine
; reports as SOLVER_ERROR:
;
;   (error "solver returned SOLVER_ERROR")
;   STP Error: internal error in 'Solver::parse': ... please report it [INTERNAL]
;
; -- an internal failure asking for a bug report, for a backend the caller
; chose. Four lines reproduce it, and the same four are what a fuzz campaign
; minimised two SOLVER_ERROR findings down to.
;
; The option is only ever refused, never honoured, when the backend cannot
; reset, so both routes have to say so.
; RUN: not %solver --SMTLIB2 --minisat %s 2>&1 | %OutputCheck %s
; CHECK: lra-extension-restart-sat
; CHECK: requires --cadical
; CHECK-NOT: SOLVER_ERROR
; CHECK-NOT: please report it
; CHECK-NOT: ^(sat|unsat)$
;
; The command line's own refusal is unchanged; misc-tests/
; lra-restart-sat-needs-factor-off.smt2 covers its other two preconditions.
; RUN: not %solver --SMTLIB2 --minisat --lra-extension-restart-sat=1 %s 2>&1 | %OutputCheck --check-prefix=CLI %s
; CLI: ^ERROR: --lra-extension-restart-sat=1 requires --cadical$
; CLI-NOT: SOLVER_ERROR
;
; With a backend that can reset, it is honoured.
; RUN: %solver --SMTLIB2 --cadical %s | %OutputCheck --check-prefix=OK %s
; OK: ^sat$
(set-logic QF_LRA)
(set-option :lra-extension-restart-sat true)
(declare-fun v () Real)
(check-sat)
(exit)
