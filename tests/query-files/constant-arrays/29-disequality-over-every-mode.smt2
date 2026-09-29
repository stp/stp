; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Every mode written: no cell differs.
(set-logic QF_ABVFP)
(assert (not (= ((as const (Array RoundingMode (_ BitVec 1))) #b0)
                (store (store (store (store (store ((as const (Array RoundingMode (_ BitVec 1))) #b1) RNE #b0) RNA #b0) RTP #b0) RTN #b0) RTZ #b0))))
(check-sat)
