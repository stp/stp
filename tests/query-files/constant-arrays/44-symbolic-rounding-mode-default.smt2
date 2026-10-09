; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; A rounding mode used only in the hidden default has a valid model value.
; Later scopes can pin it to different modes without retaining old bindings.
(set-option :produce-models true)
(set-logic QF_ABVFP)
(declare-fun mode () RoundingMode)
(declare-fun a () (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
(assert (= a ((as const (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
             (fp.roundToIntegral mode ((_ to_fp 8 24) #x3fc00000)))))
; CHECK: ^sat$
(check-sat)
; CHECK: ^\(mode (RNE|RNA|RTP|RTN|RTZ)\)$
(get-value (mode))
(push 1)
(assert (= mode RTZ))
; CHECK: ^sat$
(check-sat)
; CHECK: #x3F800000
(get-value ((fp.to_ieee_bv (select a #x02))))
(push 1)
(assert (not (fp.eq (select a #x02) ((_ to_fp 8 24) #x3f800000))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
(pop 1)
(push 1)
(assert (= mode RNE))
; CHECK: ^sat$
(check-sat)
; CHECK: #x40000000
(get-value ((fp.to_ieee_bv (select a #x02))))
(pop 1)
; CHECK: ^sat$
(check-sat)
