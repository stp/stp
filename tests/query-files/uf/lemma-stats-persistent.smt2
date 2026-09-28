; RUN: %solver --uf-propagate-equalities=0 -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck %s
; --uf-propagate-equalities=0: this test exercises the refinement loop on a
; top-level equality, which the pre-lowering pass would otherwise settle before
; any lemma is needed.
; CHECK: ^UF: installed congruence lemma 1 for f \(block guarded\)$
; CHECK: ^unsat$
; CHECK-NOT: installed congruence lemma 2
; The persistent adapter carries this refinement under the exact-stack block
; guard, and -s names the host. --uf-ackermann=off keeps
; the lemma dynamic; eagerly encoded, this query would install none.
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
