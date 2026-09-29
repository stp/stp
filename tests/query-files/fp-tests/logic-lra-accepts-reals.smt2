; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
;
; The LRA variants of the floating-point logics are the floating-point
; logics plus the theory of reals: Real declarations and linear arithmetic
; are part of them.
(set-logic QF_BVFPLRA)
(declare-fun r () Real)
(assert (> r 0.0))
(check-sat)
