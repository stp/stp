; Boolean cells and indices print as true/false, including completed arrays.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
; RUN: %solver --array-ackermann-budget=0 %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic ALL)
(declare-const a (Array Bool Bool))
(declare-const p Bool)
(assert (select a false))
(assert (not (select a true)))
(assert p)
; CHECK-NEXT: ^sat$
(check-sat)
; CHECK: \(select \|a\| false\).*true
; CHECK-NEXT: \(select \|a\| true\).*false
; CHECK-NEXT: \(select \|a\| \|p\|\).*false
(get-value ((select a false) (select a true) (select a p)))
; CHECK: \(define-fun \|a\| \(\) \(Array Bool Bool\)
; CHECK-NOT: #b
(get-model)
(push 1)
(assert (not p))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)
; CHECK: \(select \|a\| false\).*true
(get-value ((select a false)))
