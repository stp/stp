; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The values a free argument is given: the smallest positive integers no
; other value in the model holds, in symbol order. The three results sit at
; their lower bounds, 10, 20 and 30, so the arguments take 1, 2 and 3 -- and
; a symbol that is not an argument of anything keeps the zero it always had.
(set-logic QF_UFLRA)
(set-option :produce-models true)
(declare-fun f (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun unrelated () Real)
(assert (>= (f a) 10.0))
(assert (>= (f b) 20.0))
(assert (>= (f c) 30.0))
; CHECK: ^sat
(check-sat)
; CHECK: (|a| 1)
; CHECK: (|b| 2)
; CHECK: (|c| 3)
; CHECK: (|unrelated| 0)
(get-value (a b c unrelated))
