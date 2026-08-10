; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A nullary define-fun of float-element array sort is a pure name for
; its body; uses of the name expand to the body, so the stored zero is
; visible through it.
(set-logic QF_ABVFP)
(declare-fun base () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(define-fun A0 () (Array (_ BitVec 2) (_ FloatingPoint 8 24)) (store base #b01 (_ +zero 8 24)))
(assert (fp.isZero (select A0 #b01)))
(assert (fp.isNormal (select A0 #b00)))
(check-sat)
