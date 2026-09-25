; RUN: %solver --SMTLIB2 --lra-presolve-subst=1 --lra-presolve-bounds=1 --lra-presolve-rows=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The Real presolve stages against the plain pipeline: solved and
; Gaussian-shaped definitions (2x + 3y = z - 1 defines x as much as
; x = t does), met bounds fixing a variable, a same-polynomial pair, and
; -- the regression that once crashed the Gaussian pass -- a second
; definition of an already-defined symbol, whose substituted form folds
; to a constant at the factory. Both runs must agree on every verdict.
; CHECK: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^unsat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun w () Real)
(assert (= (+ (* 2 x) (* 3 y)) (- z 1)))
(assert (= (+ x y) 5))
(assert (<= z 10))
(assert (<= w 4))
(assert (>= w 4))
(assert (<= (+ w y) 9))
(assert (<= (+ w y) 12))
(check-sat)
(push 1)
(assert (= x 7))
(check-sat)
(pop 1)
(push 1)
(assert (>= y 0))
(check-sat)
(push 1)
(assert (= y (- 10)))
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(exit)
