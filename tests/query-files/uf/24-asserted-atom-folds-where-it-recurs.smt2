; A top-level assertion holds wherever else it occurs. The guard of the
; implication below is asserted outright, so the implication collapses to
; its consequent, the equality x = #x05 that only the consequent stated
; reaches (f x), and the query folds before anything is bit-blasted. The
; skeleton pass would find the same fact; this pins the rewrite itself, with
; the skeleton switched off, so the two cannot cover for each other.
;
; RUN: %solver -s --uninterpreted-functions --uf-skeleton-preproc=0 --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --uf-skeleton-preproc=0 --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: UF: pre-lowering substituted [0-9]+ symbol\(s\) and [0-9]+ application\(s\) and [0-9]+ asserted atom\(s\) in [0-9]+ round\(s\), 0 application\(s\) remain
; CHECK-NOT: installed congruence lemma
; CHECK: ^unsat$
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const w (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (bvule y #x10))
(assert (=> (bvule y #x10) (= x #x05)))
(assert (= (f #x05) #x00))
(assert (= z (bvudiv w (bvadd (f x) #x01))))
(assert (distinct z w))
(check-sat)
