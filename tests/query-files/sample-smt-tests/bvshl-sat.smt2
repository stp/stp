; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |Y| () (_ BitVec 2) #b01)
; The companion of bvshl-unsat.smt2.  0b11 shifted left gives 11, 10, 00, 00
; as the shift amount runs 0..3, so 10 is reachable and only by shifting one
; place: the model has to report that amount, not merely "some Y exists".
; Converted from sample-cvc-tests/bvshl-invalid.cvc.
(set-logic QF_BV)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun X () (_ BitVec 2))
(declare-fun Y () (_ BitVec 2))
(assert (= X #b11))
(assert (= (bvshl X Y) #b10))
(check-sat)
(get-model)
