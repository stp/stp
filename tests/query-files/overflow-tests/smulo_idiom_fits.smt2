; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; -128 * 1 = -128 fits in 8 bits and is negative, so the high bits of the
; sign-extended product are all one and the all-zero form is unsat.
(define-fun hi () (_ BitVec 9)
  ((_ extract 15 7) (bvmul ((_ sign_extend 8) x) ((_ sign_extend 8) y))))
(assert (= x #x80))
(assert (= y #x01))
(assert (= hi #b111111111))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
