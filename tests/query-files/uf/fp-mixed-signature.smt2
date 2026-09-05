; Every admitted sort in one signature, in both directions, in the shape of
; 08-mixed-signature-roundtrip.smt2. The floating-point positions are the
; ones that move between the source sort and the packed carrier, so a
; lowering that dropped or mistyped one shows up here as a wrong answer
; rather than as a missing lemma.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=on --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(declare-fun g (RoundingMode (_ FloatingPoint 8 24) (_ BitVec 8) Bool)
               (_ FloatingPoint 8 24))
(declare-const r RoundingMode)
(declare-const s RoundingMode)
(declare-const u (_ FloatingPoint 8 24))
(declare-const v (_ FloatingPoint 8 24))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const b Bool)
(push 1)
(assert (= r s))
(assert (= u v))
(assert (= x y))
(assert (distinct (g r u x b) (g s v y b)))
(check-sat)
(pop 1)
(push 1)
; Only the floating-point position disagrees, and it disagrees as *values*:
; nothing forces the results equal.
(assert (= r s))
(assert (= x y))
(assert (not (= u v)))
(assert (distinct (g r u x b) (g s v y b)))
(check-sat)
(pop 1)
(echo "REACHED-END")
