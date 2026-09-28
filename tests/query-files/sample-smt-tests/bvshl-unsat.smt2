; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Shifting 0b11 left by any 2-bit amount gives 11, 10, 00 or 00, so the
; result can never be 01.  Converted from sample-cvc-tests/bvshl-valid.cvc.
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun X () (_ BitVec 2))
(declare-fun Y () (_ BitVec 2))
(assert (= X #b11))
(assert (= (bvshl X Y) #b01))
(check-sat)
(exit)
