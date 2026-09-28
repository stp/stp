; The r < b order law, refutable by the lemma block's propagation alone:
; asserting a remainder at or above a nonzero divisor contradicts
; b != 0 -> r < b directly.
; RUN: %solver --bb.div-lemmas 1 %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 24))
(declare-fun b () (_ BitVec 24))
(assert (bvugt b (_ bv0 24)))
(assert (bvuge (bvurem a b) b))
(check-sat)
