; get-option reports the options set-option honours, and "unsupported"
; otherwise.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
; CHECK-NEXT: ^false
(get-option :print-success)
; CHECK-NEXT: ^false
(get-option :produce-models)
(set-option :produce-models true)
; CHECK-NEXT: ^true
(get-option :produce-models)
; CHECK-NEXT: ^"stdout"
(get-option :diagnostic-output-channel)
; CHECK-NEXT: ^unsupported
(get-option :produce-proofs)
; CHECK-NEXT: ^unsupported
(get-option :some-unknown-option)
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
