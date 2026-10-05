; REQUIRES: highs
; RUN: %solver --SMTLIB2 --lra-highs-lp=1 --lra-highs-mip=0 --max-time=15 %s 2>&1 | %OutputCheck %s
; CHECK: ^sat$
; Before the small-matrix-value guard, STP aborted in HiGHS
; getDualRayInterface with Assertion `has_invert' failed.
; Run with --lra-highs-lp=1. HiGHS drops the 1e-14 matrix entry.
; Expected answer: sat (for example, x = 100000000000000).
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (<= 1 (* x 0.00000000000001)))
(check-sat)
