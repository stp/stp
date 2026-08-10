; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; The body of a define-fun must match the declared result sort. Regression
; test: nullary floating-point define-funs used to accept any body silently,
; deferring the failure to a confusing message at the use site.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
; CHECK: does not match the declared result sort
(define-fun g () (_ FloatingPoint 11 53) x)
(check-sat)
