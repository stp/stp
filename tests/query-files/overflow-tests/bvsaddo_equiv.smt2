; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvsaddo(x,y) iff operands share a sign that differs from the sum's sign.
(assert (not (= (bvsaddo x y)
  (and (= ((_ extract 7 7) x) ((_ extract 7 7) y))
       (distinct ((_ extract 7 7) x) ((_ extract 7 7) (bvadd x y)))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
