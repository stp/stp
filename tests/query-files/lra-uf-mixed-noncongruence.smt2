; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The declared-sort arguments are free to differ, so nothing forces the two
; results together whatever the Real arguments do.
(set-logic QF_UFLRA)
(declare-sort S 0)
(declare-fun g (Real S) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun s () S)
(declare-fun t () S)
(assert (= a b))
(assert (not (= (g a s) (g b t))))
; CHECK: ^sat
(check-sat)
