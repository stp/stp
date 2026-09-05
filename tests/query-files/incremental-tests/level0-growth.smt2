; Base-level assertions between check-sats, without any push: with
; --incremental the driver asserts each as a permanent unit clause when it
; arrives, narrowing the space monotonically.
; RUN: %solver --incremental %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x #x10))
; CHECK-NEXT: ^sat
(check-sat)
(assert (bvult x #x08))
; CHECK-NEXT: ^sat
(check-sat)
(assert (bvugt x #x0a))
; x < 8 and x > 10 together are unsatisfiable
; CHECK-NEXT: ^unsat
(check-sat)
; and level-0 unsat is permanent
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
