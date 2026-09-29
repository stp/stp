; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; No finite binary64 lies strictly between 1 and 1 + 2^-52.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 11 53))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (> (fp.to_real x) 1.0))
(assert (< (fp.to_real x) (+ 1.0 (/ 1 4503599627370496))))
(check-sat)
