; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A nullary array-sorted define-fun is a pure name for its body, so it
; is accepted with or without --array-equality (QF_ABVFP inputs use
; them with no whole-array equality in sight); uses of the name expand
; to the body.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 2) (_ BitVec 2)) (store base (_ bv0 2) (_ bv1 2)))
(assert (= (select A0 (_ bv0 2)) (_ bv1 2)))
(check-sat)
