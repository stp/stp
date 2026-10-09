; REQUIRES: cryptominisat
;
; Here rather than beside the lra-* files because it names its backend, and
; those are swept with each backend's flag prepended.
;
; The SAT search reset needs a backend that can do one, which CryptoMiniSat
; cannot. Which of the two refusals arrives depends on the build: one with
; CaDiCaL says to name it, one without says to build it in.
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
; RUN: not %solver --SMTLIB2 --cryptominisat %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "option 'lra-extension-restart-sat': --lra-extension-restart-sat=1 requires (--cadical|a build with CaDiCaL) \[OPTION_
; CHECK-NOT: SOLVER_ERROR
; CHECK-NOT: please report it
; CHECK-NOT: ^(sat|unsat)$
;
; The command line says the same words, where it has always checked for the
; reset: after the combination with a Real session, which
; lra-extension-controls-need-batch.smt2 pins, and before the other two
; preconditions in misc-tests/lra-restart-sat-needs-factor-off.smt2.
; RUN: not %solver --SMTLIB2 --cryptominisat --lra-extension-restart-sat=1 %s 2>&1 | %OutputCheck --check-prefix=CLI %s
; CLI: ^ERROR: --lra-extension-restart-sat=1 requires (--cadical|a build with CaDiCaL)$
; CLI-NOT: SOLVER_ERROR
(set-logic QF_LRA)
(set-option :lra-extension-restart-sat true)
(declare-fun v () Real)
(check-sat)
(exit)
