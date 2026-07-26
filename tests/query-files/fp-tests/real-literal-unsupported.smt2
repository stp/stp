; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; Conversion from a real literal is deliberately unsupported (no
; QF_FP/QF_BVFP/QF_ABVFP benchmark uses it), but the diagnostic must say so
; and point at the supported spellings, not stop at a bare syntax error.
; CHECK: real literals are not supported
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x ((_ to_fp 8 24) RNE 1.5)))
(check-sat)
