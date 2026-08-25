; A remainder never exceeds its dividend, over a zero divisor included --
; where the remainder is the dividend. This one STP already decided before
; the fact was added; it is here so that a change which breaks it is caught.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvugt (bvurem a b) a))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
