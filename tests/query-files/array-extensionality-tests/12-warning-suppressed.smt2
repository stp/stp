; RUN: %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK-NOT-L: STP doesn't handle array extensionality
; CHECK: ^sat
; The array-extensionality warning is suppressed when the feature is on.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (= a b))
(check-sat)
