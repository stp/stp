; RUN: %solver %s | %OutputCheck %s
;
; get-model defines every function with a Real argument or result. Such a
; function has no packed seed, so its cases come from the observed
; applications, valued by the exact Real model, and every other tuple takes
; the codomain's zero.
(set-logic QF_UFLRA)
(set-option :produce-models true)
(declare-fun f (Real) Real)
(declare-fun g (Bool) Real)
(declare-fun h (Real Real) Real)
(declare-fun q (Real) Bool)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Bool)
(assert (> (f x) (+ (f y) 1.0)))
(assert (> (g b) 2.0))
(assert (= (h x 1.0) 5.0))
(assert (q x))
(assert (not (q y)))
(check-sat)
(get-model)
; CHECK: ^sat
; CHECK: ^\(define-fun \|f\| \(\(x0 Real\)\) Real$
; CHECK-NEXT: ^  \(ite \(= x0 .*\) .* \(ite \(= x0 .*\) .* 0\)\)\)$
; CHECK: ^\(define-fun \|g\| \(\(x0 Bool\)\) Real$
; CHECK-NEXT: ^  \(ite \(= x0 (true|false)\) .* 0\)\)$
; CHECK: ^\(define-fun \|h\| \(\(x0 Real\) \(x1 Real\)\) Real$
; CHECK-NEXT: ^  \(ite \(and \(= x0 .*\) \(= x1 1\)\) 5 0\)\)$
; CHECK: ^\(define-fun \|q\| \(\(x0 Real\)\) Bool$
; CHECK-NEXT: ^  \(ite \(= x0 .*\) (true|false) \(ite \(= x0 .*\) (true|false) false\)\)\)$
