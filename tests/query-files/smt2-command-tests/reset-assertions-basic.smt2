; reset-assertions must empty the assertion stack, so an unsatisfiable
; conjunction stops being unsatisfiable afterwards.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (and (= x #x1) (= x #x2)))
; CHECK-NEXT: ^unsat
(check-sat)
(reset-assertions)
; CHECK-NEXT: ^sat
(check-sat)
