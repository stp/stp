; RUN: %solver %s | %OutputCheck %s
;
; SMT-LIB's RoundingMode sort has exactly five values, but the 5-bit
; bitvector that carries one has 32. Declaring a RoundingMode symbol asserts
; the five-way one-hot constraint, so no model can pick an encoding that
; denotes no rounding mode. Regression test: "r differs from all five modes"
; used to answer sat (with r = #b00000).
(set-logic QF_FP)
(declare-const r RoundingMode)
(assert (not (= r roundNearestTiesToEven)))
(assert (not (= r roundNearestTiesToAway)))
(assert (not (= r roundTowardPositive)))
(assert (not (= r roundTowardNegative)))
(assert (not (= r roundTowardZero)))
; CHECK: ^unsat
(check-sat)
