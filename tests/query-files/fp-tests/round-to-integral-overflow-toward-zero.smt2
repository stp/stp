; RUN: %solver %s | %OutputCheck %s
;
; Rounding toward zero never leaves the top binade, so no finite rounds to
; an infinity under it, in any format.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 2 3))
(declare-const t (_ FloatingPoint 2 3))
(assert (= t (fp.roundToIntegral RTZ x)))
(assert (fp.isInfinite t))
(assert (not (fp.isInfinite x)))
(check-sat)
