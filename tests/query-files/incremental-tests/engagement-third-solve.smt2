; An explicit engagement threshold starts at the named real solve. This
; keeps the small check-3 boundary test independent of the theory-specific
; default (pure QF_BV/QF_ABV now uses 32).
; RUN: %solver -s --incremental-auto-engage-at 3 %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x #x80))
(push 1)
(assert (bvult x #x40))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvult x #x20))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvuge x #x80))
; CHECK: Incremental: encoded
; CHECK: ^unsat
(check-sat)
(pop 1)
(exit)
