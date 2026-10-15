; REQUIRES: highs
; RUN: %solver --SMTLIB2 --lra-highs-lp=1 --lra-highs-mip=0 --max-time=15 %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat$
; Regression for HiGHS #3352: HFactor::zeroCol asserts on pivot tolerance
; in the pinned HiGHS revision.
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (< (* 3375000 (- d b)) d))
(assert (>= (+ d (- b) (* (- 1000) a) c) 1))
(assert (< (+ (* (- 506250000) a) d (- b) c) 0))
(assert (<= (+ a c) 0))
(assert (<= (+ (* 11390625000000 (- d b)) c) 0))
(check-sat)
