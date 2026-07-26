; Declarations made at the base level survive reset-assertions, unlike reset.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
(reset-assertions)
; x must still be declared here.
(assert (= x #x2))
; CHECK-NEXT: ^sat
(check-sat)
