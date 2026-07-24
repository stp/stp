; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; An array-valued if-then-else (true branch) is eliminated to a fresh
; array with guarded equalities.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun p () Bool)
(declare-fun i () (_ BitVec 2))
(assert p)
(assert (= (ite p a b) c))
(assert (distinct (select a i) (select c i)))
(check-sat)
