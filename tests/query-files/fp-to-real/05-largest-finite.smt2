; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The largest finite Float16 is 65504, and nothing finite in the format is
; larger.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 5 11))
(assert (or (not (= (fp.to_real (fp #b0 #b11110 #b1111111111)) 65504.0))
            (and (not (fp.isNaN x)) (not (fp.isInfinite x)) (> (fp.to_real x) 65504.0))))
(check-sat)
