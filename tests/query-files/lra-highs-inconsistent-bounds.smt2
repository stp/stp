; REQUIRES: highs
; RUN: %solver --SMTLIB2 --lra-highs-lp=1 --lra-highs-mip=0 --max-time=15 %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat$
; Before the inconsistent-bounds guard, STP aborted in HiGHS getDualRayInterface
; with Assertion `has_invert' failed. Run with --lra-highs-lp=1.
; Expected answer: unsat.
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (<= x 1))
(assert (>= x 2))
(check-sat)
