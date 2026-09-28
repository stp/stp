; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A define-fun with Real formals. These are macro parameters, not
; uninterpreted functions: the arguments are substituted into the body at
; each application, so nothing of Real sort survives that the linear
; fragment does not already handle. max(2, 7) = 7.
(set-logic QF_LRA)
(define-fun mymax ((x Real) (y Real)) Real (ite (< x y) y x))
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a 2.0))
(assert (= b 7.0))
(assert (= (mymax a b) 7.0))
; CHECK: ^sat
(check-sat)
