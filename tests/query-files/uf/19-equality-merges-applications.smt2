; A top-level equality between two arguments makes their applications one
; application before lowering, so the query is refuted without a single
; congruence lemma. Under --uf-propagate-equalities=0 the same query needs
; the refinement loop (see batched-congruence-lemmas.smt2 for that trace).
;
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: UF: pre-lowering substituted 2 symbol\(s\) and 0 application\(s\)
; CHECK-NOT: installed congruence lemma
; CHECK: ^unsat$
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (= x y))
(assert (= y z))
(assert (distinct (f x) (f z)))
(check-sat)
