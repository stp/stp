; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; DR-T-FP-BOUNDARY-01 / T-UF-07: a Bool actual containing an
; FP-derived predicate is named at the UF boundary, then the naming
; equation is lowered by the FP pipeline; congruence still binds.
(set-logic QF_BVFP)
(declare-fun u () (_ FloatingPoint 8 24))
(declare-fun v () (_ FloatingPoint 8 24))
(declare-fun f (Bool) (_ BitVec 4))
(assert (distinct (f (fp.lt u v)) (f (fp.lt u v))))
(check-sat)
