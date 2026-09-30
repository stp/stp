; Array equality keeps source selectors while its graph and lemmas remain
; owned by the completed block. Dropping a source retracts its consequences.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --ackermanize %s | %OutputCheck %s
; RUN: %solver --array-ackermann-budget=0 %s | %OutputCheck %s
; RUN: %solver --incremental-core-only %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 32) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 32) (_ BitVec 8)))
(declare-const i (_ BitVec 32))
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (! (= a b) :named same_array))
(assert (! r :named irrelevant))
(push 1)
(assert (! (distinct (select a i) (select b i)) :named different_reads))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|same_array\| \|different_reads\|\)$
(get-unsat-core)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)

(assert (=> p (distinct (select a i) (select b i))))
; CHECK-NEXT: ^unsat$
(check-sat-assuming (p q))
; CHECK-NEXT: ^\(\|same_array\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\|p\|\)$
(get-unsat-assumptions)
; CHECK-NEXT: ^sat$
(check-sat-assuming (q))

(push 1)
(assert (! p :named trigger))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|same_array\| \|trigger\|\)$
(get-unsat-core)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)

; An unnamed theory contradiction needs no named assertions, even if a named
; selector is present in the same block.
(assert (distinct (select a i) (select b i)))
(assert (= a b))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\)$
(get-unsat-core)
