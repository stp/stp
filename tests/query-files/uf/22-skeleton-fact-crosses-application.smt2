; The equality x = #x05 is never stated at the top level: it is the resolvent
; of two clauses, which no rewrite reads but the Boolean structure forces.
; The skeleton pass surfaces it, and the pre-lowering rewrite then sends
; (f x) to (f #x05) -- which the query pins to #x00 -- so the quotient below
; is w and the query is refuted with no divider built and no lemma learned.
;
; RUN: %solver -s --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: UF: pre-lowering substituted [0-9]+ symbol\(s\) and [0-9]+ application\(s\) in [0-9]+ round\(s\) using [0-9]+ skeleton fact\(s\), 0 application\(s\) remain
; CHECK-NOT: installed congruence lemma
; CHECK: ^unsat$
;
; Without the skeleton the fact stays buried: both applications survive
; lowering and the congruence machinery has to relate them.
; RUN: %solver -s --uninterpreted-functions --uf-skeleton-preproc=0 --incremental=off %s 2>&1 | %OutputCheck --check-prefix=NOSKEL %s
; NOSKEL-NOT: skeleton fact
; NOSKEL: 2 application\(s\) remain
; NOSKEL: ^unsat$
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const q Bool)
(declare-const x (_ BitVec 8))
(declare-const w (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (or (= x #x05) q))
(assert (or (= x #x05) (not q)))
(assert (= (f #x05) #x00))
(assert (= z (bvudiv w (bvadd (f x) #x01))))
(assert (distinct z w))
(check-sat)
