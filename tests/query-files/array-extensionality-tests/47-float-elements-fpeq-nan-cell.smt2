; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Equal arrays have =-equal cells, yet a cell can still refute fp.eq
; against itself: exactly when it holds NaN.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(assert (= a b))
(assert (not (fp.eq (select a #b00) (select b #b00))))
(check-sat)
