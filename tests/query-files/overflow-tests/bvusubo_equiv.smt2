; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvusubo(x,y) iff the unsigned subtraction borrows, i.e. iff x <u y.
(assert (not (= (bvusubo x y) (bvult x y))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
