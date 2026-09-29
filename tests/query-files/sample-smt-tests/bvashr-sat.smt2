; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |Y| () (_ BitVec 3) #b001)
; The companion of bvashr-unsat.smt2.  0b100 is -4, so shifting it right
; arithmetically gives 100, 110, then 111 from two places on.  110 is
; reachable and only by shifting one place, which pins the model value of the
; shift amount and so checks that the sign bit really is the bit replicated.
; Converted from sample-cvc-tests/bvashr-invalid.cvc, which asked for the
; result 11 that every shift amount produced and so pinned nothing.
(set-logic QF_BV)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun X () (_ BitVec 3))
(declare-fun Y () (_ BitVec 3))
(assert (= X #b100))
(assert (= (bvashr X Y) #b110))
(check-sat)
(get-model)
