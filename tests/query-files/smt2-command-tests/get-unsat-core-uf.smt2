; Named assertions and user assumptions stay individually tracked through UF
; lowering, including eager congruence and lemmas generated during refinement.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --uf-ackermann=off --uf-lemmas-per-round=1 %s | %OutputCheck %s
; RUN: %solver --uf-ackermann=on %s | %OutputCheck %s
; RUN: %solver --incremental-core-only %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_UFBV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
; A separate symmetry-breaking opportunity must not replace the conditional
; theory block with a completed root that lost the source selectors.
(declare-const u (_ BitVec 8))
(declare-const v (_ BitVec 8))
(declare-const w (_ BitVec 8))
(assert (distinct u v w))
(assert (! (= x y) :named same_argument))
(assert (! r :named irrelevant))
(push 1)
(assert (! (distinct (f x) (f y)) :named different_results))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|same_argument\| \|different_results\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\|same_argument\| \|different_results\|\)$
(get-unsat-core)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)

(assert (=> p (distinct (f x) (f y))))
; CHECK-NEXT: ^unsat$
(check-sat-assuming (p q))
; CHECK-NEXT: ^\(\|same_argument\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\|p\|\)$
(get-unsat-assumptions)
; CHECK-NEXT: ^sat$
(check-sat-assuming (q))

; Reusing the term as an assertion at the same scope must use its current name.
(push 1)
(assert (! p :named trigger))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|same_argument\| \|trigger\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\)$
(get-unsat-assumptions)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)
