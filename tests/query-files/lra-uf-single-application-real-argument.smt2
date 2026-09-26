; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; One application of a Boolean-valued function with a Real argument. Applied
; once, the function has no pairs to constrain, so its actuals are never
; named -- and the model replay, which used to decide from the named actuals
; whether a Real was involved, saw none and walked the evaluator into the
; Real term. The signature says what the actuals would have.
(set-logic QF_UFLRA)
(declare-sort S 0)
(declare-fun f (S Real) Bool)
(declare-fun v () Real)
(declare-fun s () S)
(assert (= 0.0 v))
(assert (f s (+ v 0.0)))
; CHECK: ^sat
(check-sat)
