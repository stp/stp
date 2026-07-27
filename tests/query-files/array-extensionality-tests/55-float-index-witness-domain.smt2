; REQUIRES: floating-point
; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The fifteen values of (_ FloatingPoint 2 2) -- fourteen non-NaN
; patterns and the one NaN -- are each pinned pointwise equal, so the
; arrays are equal: the disequality may not be "witnessed" at the
; second NaN bit pattern, which denotes no sixteenth index. (Answered
; sat before the witness index was confined to denoting patterns.)
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 2 2) (_ BitVec 8)))
(declare-fun b () (Array (_ FloatingPoint 2 2) (_ BitVec 8)))
(assert (not (= a b)))
(assert (= (select a (fp #b0 #b00 #b0)) (select b (fp #b0 #b00 #b0))))
(assert (= (select a (fp #b0 #b00 #b1)) (select b (fp #b0 #b00 #b1))))
(assert (= (select a (fp #b0 #b01 #b0)) (select b (fp #b0 #b01 #b0))))
(assert (= (select a (fp #b0 #b01 #b1)) (select b (fp #b0 #b01 #b1))))
(assert (= (select a (fp #b0 #b10 #b0)) (select b (fp #b0 #b10 #b0))))
(assert (= (select a (fp #b0 #b10 #b1)) (select b (fp #b0 #b10 #b1))))
(assert (= (select a (fp #b0 #b11 #b0)) (select b (fp #b0 #b11 #b0))))
(assert (= (select a (fp #b0 #b11 #b1)) (select b (fp #b0 #b11 #b1))))
(assert (= (select a (fp #b1 #b00 #b0)) (select b (fp #b1 #b00 #b0))))
(assert (= (select a (fp #b1 #b00 #b1)) (select b (fp #b1 #b00 #b1))))
(assert (= (select a (fp #b1 #b01 #b0)) (select b (fp #b1 #b01 #b0))))
(assert (= (select a (fp #b1 #b01 #b1)) (select b (fp #b1 #b01 #b1))))
(assert (= (select a (fp #b1 #b10 #b0)) (select b (fp #b1 #b10 #b0))))
(assert (= (select a (fp #b1 #b10 #b1)) (select b (fp #b1 #b10 #b1))))
(assert (= (select a (fp #b1 #b11 #b0)) (select b (fp #b1 #b11 #b0))))
(check-sat)
