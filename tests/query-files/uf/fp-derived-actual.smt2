; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A Bool actual containing an FP-derived predicate is named at the UF
; boundary before the FP pipeline lowers its naming equation. No UF_APPLY may
; cross that boundary, and congruence must still bind the two applications.
(set-logic QF_BVFP)
(declare-fun u () (_ FloatingPoint 8 24))
(declare-fun v () (_ FloatingPoint 8 24))
(declare-fun f (Bool) (_ BitVec 4))
(assert (distinct (f (fp.lt u v)) (f (fp.lt u v))))
(check-sat)
