; RUN: %solver %s | %OutputCheck %s
;
; fp.roundToIntegral in a format whose exponent field is two bits wide.
; SymFPU's rounding collar widens the significand by one bit and shifts by
; the exponent; with eb = 2 and sb a power of two, the width it computed for
; that shift wrapped, and 1.0 rounded to something other than 1.0. Every
; integer is its own rounding, so this is unsat in every mode.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 2 4))
(declare-const t (_ FloatingPoint 2 4))
(assert (= t (fp.roundToIntegral RNE x)))
(assert (= x (fp #b0 #b01 #b000)))
(assert (not (= t (fp #b0 #b01 #b000))))
(check-sat)
