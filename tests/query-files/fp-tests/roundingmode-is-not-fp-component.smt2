; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)

; The fp constructor accepts source BitVec terms, not carrier-compatible
; RoundingMode terms.
; CHECK: sign, exponent and significand must be bitvectors
(assert (fp.isNaN (fp #b0 RNE #b0000)))
(check-sat)
