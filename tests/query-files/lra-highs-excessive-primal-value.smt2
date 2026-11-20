; REQUIRES: highs
; RUN: %solver --SMTLIB2 --lra-highs-lp=1 --lra-highs-mip=0 --max-time=15 %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat$
; Regression for HiGHS #3351: HEkk::rebuildReason previously asserted on
; an excessive primal value.
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< (+ (- y z) (* x 0.000001)) 0 y (* x 10000000)))
(assert (>= (- y z) 10000000000000000))
(check-sat)
