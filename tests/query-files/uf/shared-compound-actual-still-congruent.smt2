; RUN: %solver --uf-propagate-equalities=0 -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uf-propagate-equalities=0 -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck %s
; --uf-propagate-equalities=0: this test exercises the refinement loop on a
; top-level equality, which the pre-lowering pass would otherwise settle before
; any lemma is needed.
; CHECK: UF: installed congruence lemma 1 for f
; CHECK: ^unsat$
;
; The other side of the lone-application rule: f reaches two applications, so
; both compound actuals are named after all, the checker can read them, and
; the refutation still needs exactly the congruence lemma it always did.
; Nothing about withholding names from a lone application may weaken this.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const p (_ BitVec 8))
(declare-const q (_ BitVec 8))
(assert (= p q))
(assert (distinct (f (bvadd p #x01)) (f (bvadd q #x01))))
(check-sat)
