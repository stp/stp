; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvuaddo(x,y) iff the unsigned sum wraps below x.
(assert (not (= (bvuaddo x y) (bvult (bvadd x y) x))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
