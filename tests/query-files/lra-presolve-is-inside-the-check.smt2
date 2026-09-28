; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck %s
;
; The model a Real solve publishes is checked against the query as it was
; written, not only against the formula presolve handed the solver.
;
; Three exact checks pass judgement on a satisfiable answer -- the core's
; own, the model verifier's, and the coordinator's re-evaluation of its
; submitted formula -- and all three read presolve's output. Without a
; record of the pre-presolve query, the five default-on presolve stages
; would be the one layer of the answer path no check covers, so a wrong
; rewrite there would reach the answer unnoticed.
;
; This query has something for presolve to do: `d` is a top-level definition
; to substitute, and the bounds on `e` are foldable. One committed model, so
; one check against the original.
; CHECK-L: "original_formula_checks":1
; CHECK: ^sat$
(set-logic QF_LRA)
(declare-fun d () Real)
(declare-fun e () Real)
(declare-fun f () Real)
(assert (= d (+ e 3)))
(assert (>= e 1))
(assert (<= e 4))
(assert (> (+ d f) 5))
(assert (< f 10))
(check-sat)
(exit)
