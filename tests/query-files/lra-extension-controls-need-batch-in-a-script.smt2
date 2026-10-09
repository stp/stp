; The command-line half of this is lra-extension-controls-need-batch.smt2,
; which cannot carry the set-options: its passing RUN lines need a file that
; names no control. Beside it rather than in misc-tests because the refusal
; is the same whichever backend the lra-* sweep prepends.
;
; The extension controls vary the batch solve's arithmetic state and a Real
; session keeps that state across check-sats, so the two cannot be combined.
; tools/stp refuses the pair before it reads the input. A script's set-option
; and the API reach neither that check nor run_check_impl, so the pair went
; through to LraCoordinator, whose refusal arrives as an exception the engine
; reports as SOLVER_ERROR:
;
;   (error "solver returned SOLVER_ERROR")
;   STP Error: internal error in 'Solver::parse': ... please report it [INTERNAL]
;
; -- an internal failure asking for a bug report, for a combination the caller
; chose. A fuzz campaign minimised four SOLVER_ERROR findings onto this pair
; and the backend one that lra-restart-sat-needs-cadical.smt2 pins.
;
; A control that is not the SAT reset, so this pins the general check rather
; than that one option's.
; RUN: not %solver --SMTLIB2 %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "option 'lra-extension-mode': --lra-extension-mode=2 cannot be combined with --lra-persistent-state=1: the LRA extension controls apply to batch solves only \[OPTION_CONFLICT\]"\)$
; CHECK-NOT: SOLVER_ERROR
; CHECK-NOT: please report it
; CHECK-NOT: ^(sat|unsat|unknown)$
(set-logic QF_LRA)
(set-option :lra-extension-mode 2)
(set-option :lra-persistent-state true)
(declare-const x Real)
(assert (> x 1))
(assert (< x 0))
(check-sat)
(exit)
