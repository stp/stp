; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (bvsmulo x y))
(assert (bvuaddo x y))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
