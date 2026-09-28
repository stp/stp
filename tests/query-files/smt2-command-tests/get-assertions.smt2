; get-assertions prints the individual asserted formulas, and an empty list
; when nothing is asserted.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
; CHECK: ^\($
; CHECK-NEXT: ^\)$
(get-assertions)
(assert (= x #x1))
; CHECK-NEXT: ^\($
; CHECK-NEXT: = \|x\|
; CHECK-NEXT: ^\)$
(get-assertions)
(reset-assertions)
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\)$
(get-assertions)
; CHECK-NEXT: ^sat
(check-sat)
