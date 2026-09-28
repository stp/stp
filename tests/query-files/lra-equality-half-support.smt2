; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; An equality E is registered as (x <= y) and (x >= y). A conflict can rest
; on just one of those halves while E itself is false, and then E's literal
; does not stand for it -- the no-good keeps the half it actually used
; rather than compressing onto E.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (or (= x y) (> z 10.0)))
(assert (<= x y))
(assert (> y x))
(assert (< z 1.0))
; CHECK: ^unsat
(check-sat)
