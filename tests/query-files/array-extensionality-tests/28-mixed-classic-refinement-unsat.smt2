; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A consistent equality component (a, b) side by side with an array c
; that is not connected to any equality. Once a = b activates the
; extensionality checker, c is nevertheless in its complete graph; its
; rule-C congruence step is the only route to unsat. Legacy read
; refinement must not be entered in this active solve.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun k () (_ BitVec 4))
(declare-fun l () (_ BitVec 4))
(assert (= a b))
(assert (= (select a i) (select b i)))
(assert (= k l))
(assert (distinct (select c k) (select c l)))
(check-sat)
