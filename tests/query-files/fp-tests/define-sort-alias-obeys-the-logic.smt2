; RUN: not %solver %s | %OutputCheck %s
; A floating-point sort is not in QF_BV's signature, including in aliases.
; CHECK: unknown sort.*Float32
; CHECK-NOT: ^sat
(set-logic QF_BV)
(define-sort MyFloat () Float32)
(declare-fun fp () (_ BitVec 8))
(assert (= fp #x01))
(check-sat)
