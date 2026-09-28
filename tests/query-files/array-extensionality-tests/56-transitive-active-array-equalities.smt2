; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; The outer equality contains an inner array equality as an array-ITE
; condition. Lowering must activate the inner equality before the outer one
; and rebuild that dependency closure for each solve.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun c () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun d () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun e () (Array (_ BitVec 1) (_ BitVec 1)))

(push 1)
(assert (= (select a #b0) (select b #b0)))
(assert (= (select a #b1) (select b #b1)))
(assert (= (ite (= a b) c d) e))
(assert (distinct (select c #b0) (select e #b0)))
(check-sat)
(pop 1)

(push 1)
(assert (distinct (select a #b0) (select b #b0)))
(assert (= (ite (= a b) c d) e))
(assert (distinct (select d #b0) (select e #b0)))
(check-sat)
(pop 1)
