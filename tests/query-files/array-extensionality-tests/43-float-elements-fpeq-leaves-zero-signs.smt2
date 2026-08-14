; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; fp.eq is weaker than =: it identifies the two zeros and refutes NaN,
; so arrays pointwise fp.eq-equal everywhere can still differ -- at a
; cell holding +zero against -zero (a NaN payload pair no longer
; counts, and pointwise fp.eq rules NaN cells out anyway).
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(assert (not (= a b)))
(assert (fp.eq (select a #b0) (select b #b0)))
(assert (fp.eq (select a #b1) (select b #b1)))
(check-sat)
