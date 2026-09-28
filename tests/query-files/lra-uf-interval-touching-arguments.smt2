; RUN: %solver --SMTLIB2 --uf-ackermann on -s %s 2>&1 | %OutputCheck %s
;
; Ranges that touch at a closed end are not apart: 5 is in both, and the
; remaining assertion puts both symbols there. The pair must keep its
; constraint, and the query is unsatisfiable because of it.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 5.0))
(assert (<= y 5.0))
(assert (<= x y))
(assert (not (= (f x) (f y))))
; CHECK: 0 impossible, 1 constraints
; CHECK: ^unsat
(check-sat)
