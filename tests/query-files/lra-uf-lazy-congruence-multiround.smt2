; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Congruence that only becomes visible once the arithmetic has settled where
; the arguments are. Nothing relates the three points syntactically -- a is
; pinned by two inequalities, b is reached through a sum -- so no amount of
; looking at the terms would have paired them; only a model does, and once one
; does the results are forced together and contradict the assertion.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (<= a b))
(assert (<= b a))
(assert (= c (+ a 0.0)))
(assert (not (= (f a) (f c))))
; CHECK: ^unsat
(check-sat)
