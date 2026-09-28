; The pin on an introduced RoundingMode symbol lives inside the exact-stack
; block that introduced it, and is retracted with that block. Introduced
; scalars are deterministic in their key node, so the identical later block
; reconstructs the identical @uf_result symbol -- and has to re-pin it, or the
; second solve answers sat where the first answered unsat.
;
; Every block below is byte-identical, so this is the same shape
; persistent-backend-rebuild-cache.smt2 stresses for the equality cache,
; narrowed to the pin.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=auto %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: ^unsat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(declare-fun k ((_ BitVec 4)) RoundingMode)
(declare-const x (_ BitVec 4))
(push 1)
(assert (distinct (k x) RNE))
(assert (distinct (k x) RTZ))
(assert (distinct (k x) RTP))
(assert (distinct (k x) RTN))
(assert (distinct (k x) RNA))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (k x) RNE))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (k x) RNE))
(assert (distinct (k x) RTZ))
(assert (distinct (k x) RTP))
(assert (distinct (k x) RTN))
(assert (distinct (k x) RNA))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (k x) RNE))
(check-sat)
(pop 1)
(push 1)
(assert (distinct (k x) RNE))
(assert (distinct (k x) RTZ))
(assert (distinct (k x) RTP))
(assert (distinct (k x) RTN))
(assert (distinct (k x) RNA))
(check-sat)
(pop 1)
(echo "REACHED-END")
