; RUN: %solver -d --congruence-candidates=1 %s | %OutputCheck %s
; RUN: %solver -d %s | %OutputCheck %s
; CHECK: ^sat
;
; The congruence pass runs before floating-point lowering, so a pairing of
; two conversions from float has to be left alone: its sub-solve would
; blast floating-point operations that have no encoding context yet.
(set-logic QF_BVFP)
(declare-fun f () Float32)
(declare-fun g () Float32)
(declare-fun x () (_ BitVec 8))
(assert (distinct (bvudiv ((_ fp.to_ubv 8) RNE f) x) (bvudiv ((_ fp.to_ubv 8) RNE g) x)))
(check-sat)
(exit)
