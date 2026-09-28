; A RoundingMode result symbol must be pinned to the five legal one-hot
; encodings. The sort has five values; its carrier has thirty-two. Without a
; pin the checker is free to hand @uf_result_kN a sixth "mode" that differs
; from all five, and the query answers sat -- a model naming no rounding mode
; at all.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
(set-logic QF_UFBVFP)
(declare-fun k ((_ BitVec 4)) RoundingMode)
(assert (distinct (k #x0) RNE))
(assert (distinct (k #x0) RTZ))
(assert (distinct (k #x0) RTP))
(assert (distinct (k #x0) RTN))
(assert (distinct (k #x0) RNA))
(check-sat)
