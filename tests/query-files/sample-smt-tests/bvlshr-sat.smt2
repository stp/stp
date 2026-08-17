; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |Y| () (_ BitVec 2) #b01)
; The companion of bvlshr-unsat.smt2.  0b11 shifted right gives 11, 01, 00,
; 00 as the shift amount runs 0..3, so 01 is reachable and only by shifting
; one place: the model has to report that amount.  Converted from
; sample-cvc-tests/bvlshr-invalid.cvc.
(set-logic QF_BV)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun X () (_ BitVec 2))
(declare-fun Y () (_ BitVec 2))
(assert (= X #b11))
(assert (= (bvlshr X Y) #b01))
(check-sat)
(get-model)
