; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; SMT-LIB requires floating-point formats to have at least 2 exponent and
; 2 significand bits. Regression test: (_ FloatingPoint 1 1) used to flow
; into the blaster and die with a misleading BVTypeCheck error about array
; selects.
; CHECK: at least 2 exponent and 2 significand bits
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 1 1))
(assert (fp.isNormal x))
(check-sat)
