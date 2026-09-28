; RUN: %solver %s | %OutputCheck %s
;
; define-fun with floating-point parameters must store and apply the
; function. Regression test: this grammar action used to be empty -- the
; function was silently dropped, and its parameter names stayed interned as
; free variables that were never declared.
(set-logic QF_FP)
(define-fun dbl ((a (_ FloatingPoint 3 5))) (_ FloatingPoint 3 5)
  (fp.add RNE a a))
(declare-fun x () (_ FloatingPoint 3 5))
(assert (fp.eq (dbl x) (fp.add RNE x x)))
(assert (fp.isNormal x))
; CHECK: ^sat
(check-sat)
