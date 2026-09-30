; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; Equality of constant arrays with symbolic defaults forces those defaults
; equal. The defaults remain visible after a contradictory scope is popped.
(set-logic QF_ABV)
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= ((as const (Array (_ BitVec 8) (_ BitVec 8))) v) ((as const (Array (_ BitVec 8) (_ BitVec 8))) w)))
(check-sat)
(push 1)
(assert (not (= v w)))
(check-sat)
(pop 1)
(check-sat)
