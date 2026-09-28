; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A nullary define-fun of array sort is a pure name for its body; a
; later reference resolves back to the body, exactly as a declared
; array symbol would.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 2) (_ BitVec 2)) (store base (_ bv0 2) (_ bv1 2)))
(assert (= (select A0 (_ bv0 2)) (_ bv1 2)))
(check-sat)
