; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A Real ite guarded by a Boolean variable rather than a Real comparison.
; A model of the Real variables alone cannot decide that condition, so the
; verifier lends the model an oracle onto the counterexample, which carries
; every Boolean value. Refusing it instead is what made these queries
; answer "unknown".
(set-logic QF_LRA)
(declare-fun p () Bool)
(declare-fun x () Real)
(declare-fun y () Real)
(assert p)
(assert (= x 4.0))
(assert (= y 9.0))
(assert (= (ite p x y) 4.0))
; CHECK: ^sat
(check-sat)
