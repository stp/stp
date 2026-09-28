; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: ( |x|  #b10 )
; CHECK-L: unsupported
; Array-valued get-value is rejected as unsupported with the option on
; (get-model prints completed array interpretations instead); scalar
; get-value keeps working in the same session.
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
