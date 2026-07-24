; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; The ite condition is unresolved, so the array if-then-else must be
; eliminated into a fresh array with guarded equalities on every
; preparation; both branches contradict c, so the query is unsat only
; while both guarded definitions are active. A repeated solve that
; lost either guard could answer sat.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun p () Bool)
(declare-fun i () (_ BitVec 2))
(assert (= (ite p a b) c))
(assert (distinct (select a i) (select c i)))
(assert (distinct (select b i) (select c i)))
(check-sat)
(check-sat)
(check-sat)
