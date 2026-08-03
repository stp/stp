; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --bit-blast-simplification=-1 %s | %OutputCheck %s
;
; fp.roundToIntegral must accept a RoundingMode variable, not only the five
; literal modes. Regression test: its grammar rule used to demand a literal,
; unlike every other rounded operation.
; The forced bit-blast simplification run also pins the pipeline invariant that
; floating-point operations are lowered before any optional bit-blaster pass.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-fun x () (_ FloatingPoint 3 5))
(assert (fp.eq (fp.roundToIntegral r x) x))
(assert (fp.isNormal x))
; CHECK: ^sat
(check-sat)
