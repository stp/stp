; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (model
; CHECK: define-fun \|a\| \(\) \(Array \(_ BitVec 2\) \(_ BitVec 2\)\).*as const
; get-model prints a valid nullary define-fun whose body is a constant
; array under stores, replayable in a conforming SMT-LIB2 solver.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (distinct a b))
(check-sat)
(get-model)
