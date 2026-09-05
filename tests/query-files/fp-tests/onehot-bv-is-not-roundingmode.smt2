; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)

; A one-hot value is not implicitly promoted from BitVec to RoundingMode.
; CHECK: expected a rounding mode
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN (fp.add #b00001 x x)))
(check-sat)
