; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK: define-fun \|a\| .*as const.*#x07
; The printed model of an array equated with a constant array fills its
; unobserved cells with the default, so the model satisfies the equality.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)))
(check-sat)
(get-model)
