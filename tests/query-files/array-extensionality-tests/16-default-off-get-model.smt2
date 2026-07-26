; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: ( define-fun |a|  (_ BitVec 2) (_ BitVec 2) #b00 #b01 )
; Without --array-equality, get-model keeps the pre-feature (legacy)
; array output byte for byte.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(assert (= (select a i) (_ bv1 2)))
(check-sat)
(get-model)
