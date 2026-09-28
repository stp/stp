; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A RoundingMode index denotes only through the five one-hot patterns,
; so arrays pointwise = at all five modes are equal: their disequality
; may not be "witnessed" at a non-denoting bit pattern of the index
; carrier. (Answered sat before the witness index was confined.)
(set-logic QF_ABVFP)
(declare-fun a () (Array RoundingMode (_ BitVec 8)))
(declare-fun b () (Array RoundingMode (_ BitVec 8)))
(assert (not (= a b)))
(assert (= (select a RNE) (select b RNE)))
(assert (= (select a RNA) (select b RNA)))
(assert (= (select a RTP) (select b RTP)))
(assert (= (select a RTN) (select b RTN)))
(assert (= (select a RTZ) (select b RTZ)))
(check-sat)
