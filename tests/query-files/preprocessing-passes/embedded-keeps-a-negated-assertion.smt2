; The trap this pass has to avoid: `not p` says p is false, and p is its own
; child, so rebuilding the assertion from its children would leave `not
; false` and drop the constraint. A query that is unsatisfiable only because
; of the negated assertion catches that immediately.
; RUN: %solver --embedded-constraints=1 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (not (bvult a b)))
(assert (bvult a b))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
