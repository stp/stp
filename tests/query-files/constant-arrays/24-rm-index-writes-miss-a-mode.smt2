; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Four of the five modes written: RTZ's cell holds both defaults.
(set-logic QF_ABVFP)
(assert (= ((as const (Array RoundingMode (_ BitVec 1))) #b0)
           (store (store (store (store ((as const (Array RoundingMode (_ BitVec 1))) #b1) RNE #b0) RNA #b0) RTP #b0) RTN #b0)))
(check-sat)
