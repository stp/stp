; The other corner of fp-nan-congruence-unsat, and the reason the boundary
; has to be a *semantic* quotient rather than any convenient normalisation.
;
; -0 and +0 compare equal under fp.eq but are distinct values under SMT-LIB's
; =, so congruence puts no obligation on f at all here and an interpretation
; separating them exists. A canonicalisation that collapsed the two zeros
; along with the NaN payloads would make this unsat, which is why it is a
; test and not a remark.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=off --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(declare-fun f ((_ FloatingPoint 8 24)) (_ BitVec 4))
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (fp.isZero x))
(assert (fp.isNegative x))
(assert (fp.isZero y))
(assert (fp.isPositive y))
(assert (distinct (f x) (f y)))
(check-sat)
(push 1)
; fp.eq does identify the two zeros, so this stays satisfiable as well: it
; asks nothing more of f than the block above.
(assert (fp.eq x y))
(check-sat)
(pop 1)
(echo "REACHED-END")
