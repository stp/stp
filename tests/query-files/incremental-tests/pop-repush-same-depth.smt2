; Pop then push back to the same depth with different content: the driver
; must key its assumptions on the current stack's formulas, never on the
; depth. A driver that cached "level 1's assumptions" by level number would
; re-assert the popped formula and answer unsat here.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x #x80))
(push 1)
(assert (bvugt x #xf0))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x10))
; same depth, different formula: must be sat
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; and the other way: sat content replaced by unsat content
(push 1)
(assert (= x #x11))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x x))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
