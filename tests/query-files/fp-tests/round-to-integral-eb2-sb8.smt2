; RUN: %solver %s | %OutputCheck %s
;
; The same collar width wrap at the next power-of-two significand: 1.0 in
; (2, 8) is an integer and rounds to itself.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 2 8))
(declare-const t (_ FloatingPoint 2 8))
(assert (= t (fp.roundToIntegral RTZ x)))
(assert (= x (fp #b0 #b01 #b0000000)))
(assert (not (= t (fp #b0 #b01 #b0000000))))
(check-sat)
