; RUN: %solver %s | %OutputCheck %s
;
; The good side of the fp.rem format limit: an exponent width of 11 (the
; binary64 ladder rung) stays supported and solves. Guards the limit in
; FloatBlaster::REM_UNROLL_LIMIT against being tightened past the formats
; that work; rem-float128-unsupported.smt2 pins the refusing side.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 11 8))
(assert (fp.isNaN (fp.rem (fp.roundToIntegral r x) x)))
; CHECK: ^sat
(check-sat)
