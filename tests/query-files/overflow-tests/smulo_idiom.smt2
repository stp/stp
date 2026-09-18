; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; The signed check as compiled code writes it: the product fits iff bits 15
; down to 7 of the sign-extended product are all zero or all one. The
; rewrite turns each equality into (not (bvsmulo x y)) with the product's
; sign. -128 * -1 = 128 does not fit, so no-overflow is unsat; -128 * 1 fits.
(define-fun hi () (_ BitVec 9)
  ((_ extract 15 7) (bvmul ((_ sign_extend 8) x) ((_ sign_extend 8) y))))
(assert (= x #x80))
(assert (or (= hi #b000000000) (= hi #b111111111)))
(assert (= y #xff))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
