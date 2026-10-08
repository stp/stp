; A setting the engine cannot honour is the check's to refuse, not something for
; the engine to discover.
;
; The command line validates the engine's view of the options before it reads
; the input, and the API validates it at construction and at every check. A
; parsed script reached neither, because its checks go through the frontend
; rather than SolverImpl::run_check_impl. So this pair -- which the command line
; refuses outright -- used to reach LraCoordinator, whose refusal arrives as an
; exception the engine reports as SOLVER_ERROR:
;
;   (error "solver returned SOLVER_ERROR")
;   STP Error: internal error in 'Solver::parse': the engine failed: solver
;   returned SOLVER_ERROR; the term manager is poisoned and refuses every later
;   call; please report it [INTERNAL]
;
; -- an internal failure asking for a bug report, for a configuration the input
; chose.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: lra-decision-polarity
; CHECK: requires --lra-theory-propagation=1
; CHECK-NOT: SOLVER_ERROR
; CHECK-NOT: please report it
; CHECK-NOT: ^(sat|unsat)$
;
; The command line's refusal is unchanged.
; RUN: not %solver --lra-decision-polarity=1 --lra-theory-propagation=0 %s 2>&1 | %OutputCheck --check-prefix=CLI %s
; CLI: requires --lra-theory-propagation=1
; CLI-NOT: SOLVER_ERROR
(set-option :produce-models true)
(set-logic QF_LRA)
(set-option :lra-theory-propagation 0)
(set-option :lra-decision-polarity true)
(declare-fun x () Real)
(assert (> x 1.0))
(assert (< x 0.0))
(check-sat)
(exit)
