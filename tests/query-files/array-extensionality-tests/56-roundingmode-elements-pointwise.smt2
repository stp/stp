; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; RoundingMode-element arrays pointwise = at every index of the domain
; are equal; the witness cells are pinned to denote modes, so no junk
; cell pattern can play the difference.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) RoundingMode))
(declare-fun b () (Array (_ BitVec 2) RoundingMode))
(assert (not (= a b)))
(assert (= (select a #b00) (select b #b00)))
(assert (= (select a #b01) (select b #b01)))
(assert (= (select a #b10) (select b #b10)))
(assert (= (select a #b11) (select b #b11)))
(check-sat)
