; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (= a b) true
; b writes #b0 at all five rounding modes over the constant array of #b1,
; so it equals a, the constant array of #b0: the model's evaluation of
; (= a b) counted the rounding-mode index's 32 carrier patterns, found an
; unwritten one, and said false.
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun a () (Array RoundingMode (_ BitVec 1)))
(declare-fun b () (Array RoundingMode (_ BitVec 1)))
(assert (= a ((as const (Array RoundingMode (_ BitVec 1))) #b0)))
(assert (= b (store (store (store (store (store ((as const (Array RoundingMode (_ BitVec 1))) #b1) RNE #b0) RNA #b0) RTP #b0) RTN #b0) RTZ #b0)))
(check-sat)
(get-value ((= a b)))
