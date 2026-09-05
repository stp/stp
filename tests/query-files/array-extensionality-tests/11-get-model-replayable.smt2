; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\($
; CHECK: define-fun \|a\| \(\) \(Array \(_ BitVec 2\) \(_ BitVec 2\)\).*as const
; get-model answers with the SMT-LIB 2.6 parenthesized list (no "model"
; keyword) of valid nullary define-funs whose bodies are constant arrays
; under stores, replayable in a conforming SMT-LIB2 solver.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (distinct a b))
(check-sat)
(get-model)
