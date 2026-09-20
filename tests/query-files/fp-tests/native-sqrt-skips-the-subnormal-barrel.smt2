; Halving an exponent compresses the range around one, so a square root can
; neither overflow nor -- unless the significand is as long as the whole
; exponent range -- land in the subnormal range. The generic rounder cannot
; know either, and built the denormalising barrel and the saturating
; overflow test for every root. float32 skips the barrel; (4,8) is one of
; the narrow formats SymFPU's own derivation says can reach a subnormal
; root, and keeps it.
;
; RUN: %solver --bb.fp-native-sqrt=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: fp-native: square-root subnormal barrels skipped: 1
; CHECK: ^sat
;
(set-logic QF_FP)
(declare-fun a () Float32)
(declare-fun b () (_ FloatingPoint 4 8))
(declare-fun c () Float32)
(declare-fun d () (_ FloatingPoint 4 8))
(assert (fp.lt (fp.sqrt RNE a) c))
(assert (fp.lt (fp.sqrt RNE b) d))
(check-sat)
(exit)
