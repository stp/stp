; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A nullary define-fun of float-element array sort expands to its
; body: the stored zero is visible through the name, and the
; whole-array disequality is satisfied by base contents that differ
; from the written cell.
(set-logic QF_ABVFP)
(declare-fun base () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(define-fun A0 () (Array (_ BitVec 2) (_ FloatingPoint 8 24)) (store base #b01 (_ +zero 8 24)))
(assert (fp.isZero (select A0 #b01)))
(assert (not (= A0 base)))
(check-sat)
