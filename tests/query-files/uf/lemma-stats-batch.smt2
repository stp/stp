; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: ^UF: installed congruence lemma 1 for f \(query local\)$
; CHECK: ^unsat$
; CHECK-NOT: installed congruence lemma 2
; With eager encoding off, the solve starts with no congruence clause and a
; refuted candidate must earn each one. This query needs exactly one
; dynamically installed, query-local lemma, and -s reports that fact.
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
