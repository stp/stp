; REQUIRES: cadical-3
;
; Here rather than beside the lra-* files because it names its backend, and
; those are swept with each backend's flag prepended. The command-line half
; is lra-restart-sat-needs-factor-off.smt2, which cannot carry the
; set-options: its passing RUN lines need a file that asks for neither.
;
; The reset copies the formula into a fresh CaDiCaL, which CaDiCaL cannot do
; once bounded variable addition is on. Only an explicit 'on' is refused: the
; unnamed default and 'auto' are turned off for the reset instead (STP.cpp).
; tools/stp refuses it before reading the input; a script's set-option reached
; neither that check nor run_check_impl, so it went through to
; LraCoordinator, whose refusal arrives as SOLVER_ERROR and an INTERNAL
; "please report it" for a combination the caller chose.
; RUN: not %solver --SMTLIB2 --cadical %s 2>&1 | %OutputCheck %s
; CHECK: ^\(error "option 'lra-extension-restart-sat': --lra-extension-restart-sat=1 requires --cadical-factor=off \[OPTION_CONFLICT\]"\)$
; CHECK-NOT: SOLVER_ERROR
; CHECK-NOT: please report it
; CHECK-NOT: ^(sat|unsat|unknown)$
(set-logic QF_LRA)
(set-option :cadical-factor on)
(set-option :lra-extension-restart-sat true)
(declare-const x Real)
(assert (> x 1))
(assert (< x 0))
(check-sat)
(exit)
