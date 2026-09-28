; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BVFP)

(push 1)
(declare-const x RoundingMode)
(assert (= x RNE))
(pop 1)

; The popped declaration must not retype this same-name BV declaration.
(declare-const x (_ BitVec 5))
(assert (= x #b00001))
; CHECK: sat
(check-sat)
