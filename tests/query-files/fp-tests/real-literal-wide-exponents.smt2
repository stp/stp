; RUN: %solver %s | %OutputCheck %s
;
; Exponent fields wider than LibBF supports still admit ordinary literals.
; For a 65-bit field, the bias is 2^64 - 1. Cover exact values, ties,
; a significand carry, both signs, and a symbolic rounding mode.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 65 4))
(assert (= r RTP))
(assert (= x ((_ to_fp 65 4) r 1.5625)))
(assert (or
  (distinct ((_ to_fp 40 4) RNE 1.5)
            (fp #b0 #x7fffffffff #b100))
  (distinct ((_ to_fp 65 4) RNE (/ 3 2))
            (fp #b0 (_ bv18446744073709551615 65) #b100))
  (distinct ((_ to_fp 65 4) RNE 0.5)
            (fp #b0 (_ bv18446744073709551614 65) #b000))
  (distinct ((_ to_fp 65 4) RTN (- (/ 25 16)))
            (fp #b1 (_ bv18446744073709551615 65) #b101))
  (distinct ((_ to_fp 65 4) RNE 1.9375)
            (fp #b0 (_ bv18446744073709551616 65) #b000))
  (distinct ((_ to_fp 65 4) RNE (- 0.0)) (_ +zero 65 4))
  (distinct x (fp #b0 (_ bv18446744073709551615 65) #b101))))
; CHECK: ^unsat
(check-sat)
