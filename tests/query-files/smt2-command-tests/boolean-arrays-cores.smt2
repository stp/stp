; Named cores and arbitrary Boolean assumptions refer to the source reads.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --array-ackermann-budget=0 %s | %OutputCheck %s
; RUN: %solver --incremental-core-only %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic ALL)
(declare-const a (Array Bool Bool))
(declare-const b (Array Bool Bool))
(declare-const p Bool)
(declare-const irrelevant Bool)
(assert (! (= a b) :named same_array))
(assert (! irrelevant :named unused))
(push 1)
(assert (! (distinct (select a p) (select b p)) :named different_reads))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|same_array\| \|different_reads\|\)$
(get-unsat-core)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)
; CHECK-NEXT: ^unsat$
(check-sat-assuming ((select a false) (not (select b false))))
; CHECK-NEXT: ^\(\|same_array\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\(select \|a\| false\) \(not \(select \|b\| false\)\)\)$
(get-unsat-assumptions)
; CHECK-NEXT: ^sat$
(check-sat-assuming ((select a false)))
