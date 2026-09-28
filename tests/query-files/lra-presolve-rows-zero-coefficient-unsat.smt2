; RUN: %solver --SMTLIB2 --lra-presolve-rows=1 %s | %OutputCheck %s
;
; The same zero-coefficient row, refuting. 0 > 5 is false however x is chosen,
; so this is unsat -- and the division-by-zero above lost the refutation, not
; just a model. The companion of lra-presolve-rows-zero-coefficient.smt2.
; CHECK-NEXT: ^unsat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun b () Bool)
(assert (> (* x 0.0) 5.0))
(assert b)
(check-sat)
(exit)
