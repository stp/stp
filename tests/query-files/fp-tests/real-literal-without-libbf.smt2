; REQUIRES: !libbf
; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; Without LibBF (cmake ran without USE_LIBBF) real literals cannot be
; converted; the refusal must say how to get the feature and how to spell
; the value without it, not stop at a bare syntax error.
; CHECK: cannot convert real literals
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x ((_ to_fp 8 24) RNE 1.5)))
(check-sat)
