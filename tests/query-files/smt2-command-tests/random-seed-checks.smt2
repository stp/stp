; Changing the seed preserves the last model/core and affects later solves,
; including incremental solves and checks with assumptions.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-option :random-seed 42)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const p Bool)
(assert (! (bvult x y) :named ordered))
; CHECK: ^sat$
(check-sat)
(set-option :random-seed 18446744073709551615)
; CHECK-NEXT: ^\($
; CHECK-NEXT: true
; CHECK-NEXT: ^\)$
(get-value ((bvult x y)))
(push 1)
(assert (! (not (bvult x y)) :named reversed))
; CHECK-NEXT: ^unsat$
(check-sat)
(set-option :random-seed 43)
; CHECK-NEXT: ^\(\|ordered\| \|reversed\|\)$
(get-unsat-core)
(pop 1)
; CHECK-NEXT: ^unsat$
(check-sat-assuming (p (not p)))
(set-option :random-seed 1)
; CHECK-NEXT: ^\(\|p\| \(not \|p\|\)\)$
(get-unsat-assumptions)
; CHECK-NEXT: ^sat$
(check-sat-assuming (p))
(set-option :random-seed 0)
; CHECK-NEXT: ^\($
; CHECK-NEXT: true
; CHECK-NEXT: ^\)$
(get-value (p))
; CHECK-NEXT: ^sat$
(check-sat)
; CHECK-NEXT: ^\($
; CHECK-NEXT: true
; CHECK-NEXT: ^\)$
(get-value ((bvult x y)))
