; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; The unsigned check as the product equal to the zero extension of its own
; low half, which the simplifier sees as the 8-wide product zero-extended:
; (not (bvumulo x y)). 16 * 16 = 256 does not fit.
(define-fun p () (_ BitVec 16) (bvmul ((_ zero_extend 8) x) ((_ zero_extend 8) y)))
(assert (= x #x10))
(assert (= y #x10))
(assert (= p ((_ zero_extend 8) ((_ extract 7 0) p))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
