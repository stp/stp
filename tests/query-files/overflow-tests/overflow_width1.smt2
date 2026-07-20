; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 1))
(assert (not (= (bvnego a) (= a #b1))))
(assert (not (= (bvuaddo a b) (bvult (bvadd a b) a))))
(assert (not (= (bvsmulo a b)
  (let ((p (bvmul ((_ sign_extend 1) a) ((_ sign_extend 1) b))))
    (distinct p ((_ sign_extend 1) ((_ extract 0 0) p)))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
