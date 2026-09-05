; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck %s
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
