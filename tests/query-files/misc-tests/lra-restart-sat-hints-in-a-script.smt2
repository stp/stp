; REQUIRES: cadical-3
;
; Here rather than beside the lra-* files because it names its backend, and
; those are swept with each backend's flag prepended. The command-line half
; is lra-restart-sat-needs-factor-off.smt2, which pins both of the reset's
; CaDiCaL preconditions; this is the second one by the script route.
;
; The decision hints hold CaDiCaL's external-propagator slot, which a search
; reset cannot carry over. tools/stp refuses the pair before it reads the
; input; a script's set-option reached neither that check nor run_check_impl,
; so it went through to LraCoordinator, whose refusal arrives as SOLVER_ERROR
; and an INTERNAL "please report it" for a combination the caller chose.
; RUN: not %solver --SMTLIB2 --cadical %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "option 'lra-extension-restart-sat': --lra-extension-restart-sat=1 cannot be combined with --array-index-hints=decide \[OPTION_CONFLICT\]"\)$
; CHECK-NOT: SOLVER_ERROR
; CHECK-NOT: please report it
; CHECK-NOT: ^(sat|unsat|unknown)$
(set-logic QF_LRA)
(set-option :array-index-hints decide)
(set-option :lra-extension-restart-sat true)
(declare-const x Real)
(assert (> x 1))
(assert (< x 0))
(check-sat)
(exit)
