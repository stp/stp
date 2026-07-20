; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvsmulo(x,y) iff the widened product isn't the sign-extension of its low 8 bits.
(assert (not (= (bvsmulo x y)
  (let ((p (bvmul ((_ sign_extend 8) x) ((_ sign_extend 8) y))))
    (distinct p ((_ sign_extend 8) ((_ extract 7 0) p)))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
