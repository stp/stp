; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The satisfiable direction, which also exercises the model path: the
; committed model is checked against the original formula, ite and all.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x 3.0))
(assert (= y 5.0))
(assert (= (ite (< x y) y x) 5.0))
; CHECK: ^sat
(check-sat)
