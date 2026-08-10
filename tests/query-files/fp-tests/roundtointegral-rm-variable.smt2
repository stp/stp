; RUN: %solver %s | %OutputCheck %s
;
; fp.roundToIntegral must accept a RoundingMode variable, not only the five
; literal modes. Regression test: its grammar rule used to demand a literal,
; unlike every other rounded operation.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-fun x () (_ FloatingPoint 3 5))
(assert (fp.eq (fp.roundToIntegral r x) x))
(assert (fp.isNormal x))
; CHECK: ^sat
(check-sat)
