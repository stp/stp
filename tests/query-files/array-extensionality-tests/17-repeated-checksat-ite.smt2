; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^unsat
; CHECK: ^unsat
; The ite condition is unresolved, so the array if-then-else is
; replaced by a fresh array with two guarded equalities; both branches
; contradict c, so the query is unsat only while both definitions are
; active.
;
; This cannot detect a lost guard, and never could: it asserts
; everything before the first check-sat and then re-runs the identical
; query, which is answered from cache without preparing again. Test 46
; splits the assertions, which is what made the loss observable. Kept
; as coverage that a repeated identical check-sat is stable.
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
