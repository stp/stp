; An extensionality conflict ends the candidate round before the active but
; consistent UF checker is allowed to install a refinement clause.
;
; RUN: %solver -s --uninterpreted-functions --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --uninterpreted-functions --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NOT: UF: installed congruence lemma
; CHECK: ^unsat
;
(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const i (_ BitVec 8))
(assert (= a b))
(assert (distinct (select a i) (select b i)))
(assert (= (f i) (f i)))
(check-sat)
