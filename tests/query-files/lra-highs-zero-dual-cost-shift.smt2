; REQUIRES: highs
; RUN: %solver --SMTLIB2 --lra-highs-lp=1 --lra-highs-mip=0 --max-time=15 %s 2>&1 | %OutputCheck %s
; CHECK: ^sat$
; Regression for HiGHS #3356: HEkkDual::shiftCost asserts on a zero shift
; while an earlier shift remains in the pinned HiGHS revision.
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
(assert (> d c))
(assert (= b 0))
(assert (= c (* 1000000000000 a)))
(assert (= 1000000000000 (* 0.000001 (- (+ a b)))))
(check-sat)
