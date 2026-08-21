; A signature that mixes RoundingMode with the sorts UFSTP already admitted,
; in both directions, in the shape of 08-mixed-signature-roundtrip.smt2. The
; first pair of applications is forced congruent and the second is not, so a
; lowering that dropped a RoundingMode position from the argument tuple would
; show up as a wrong unsat here rather than as a missing lemma.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(declare-fun g (RoundingMode (_ BitVec 8) Bool) RoundingMode)
(declare-const r RoundingMode)
(declare-const s RoundingMode)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const b Bool)
(push 1)
(assert (= r s))
(assert (= x y))
(assert (distinct (g r x b) (g s y b)))
(check-sat)
(pop 1)
(push 1)
; Only the bit-vector position agrees, so nothing forces the results equal.
(assert (distinct r s))
(assert (= x y))
(assert (distinct (g r x b) (g s y b)))
(check-sat)
(pop 1)
(echo "REACHED-END")
