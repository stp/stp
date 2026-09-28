; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A rounding-mode index sort has five values, however many patterns its
; carrier has: writes at all five cover every cell, so a store chain over one
; constant array can equal another constant array.
(set-logic QF_ABVFP)
(assert (= ((as const (Array RoundingMode (_ BitVec 1))) #b0)
           (store (store (store (store (store ((as const (Array RoundingMode (_ BitVec 1))) #b1) RNE #b0) RNA #b0) RTP #b0) RTN #b0) RTZ #b0)))
(check-sat)
