; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The same shape is satisfiable when the condition may hold: choosing
; the then-branch discharges the equality by reflexivity, leaving the
; differing cell free to differ.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun c () Bool)
(declare-fun k () (_ BitVec 8))
(assert (= (ite c a b) a))
(assert (distinct (select a k) (select b k)))
(check-sat)
