; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (x #b10)
; CHECK-L: (a ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00))
; Scalar and array values are both available from the same model.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))
(assert (= a b))
(assert (= x #b10))
(check-sat)
(get-value (x))
(get-value (a))
