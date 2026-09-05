; Repeated resets, and a reset with nothing asserted, are both fine. The
; assertion machinery must keep working after each one.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(reset-assertions)
(declare-fun x () (_ BitVec 4))
(assert (and (= x #x1) (= x #x2)))
; CHECK-NEXT: ^unsat
(check-sat)
(reset-assertions)
(reset-assertions)
(declare-fun x () (_ BitVec 4))
(assert (= x #x4))
; CHECK-NEXT: ^sat
(check-sat)
(reset-assertions)
(push 1)
(declare-fun x () (_ BitVec 4))
(assert (and (= x #x5) (= x #x6)))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat
(check-sat)
