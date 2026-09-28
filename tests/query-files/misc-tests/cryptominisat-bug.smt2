; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |X| () (_ BitVec 4) #xA)
; A four-bit addition that wraps: 6 + X = 0 has the single solution X = 10.
; Converted from cryptominisat-bug.cvc, which only checked that the answer
; was Invalid -- so it passed even if the value came back wrong.
(set-logic QF_BV)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun X () (_ BitVec 4))
(assert (= #x0 (bvadd #x6 X)))
(check-sat)
(get-model)
