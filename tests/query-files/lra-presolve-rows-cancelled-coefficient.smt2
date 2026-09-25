; RUN: %solver --SMTLIB2 --lra-presolve-rows=1 %s | %OutputCheck %s
;
; The zero arrives by folding rather than as a literal: (+ (- 5) 5) is 0 at
; the factory, so the product is (* x 0) by the time the presolve sees it.
; The shape murxla's QF_LRA differential lane actually found.
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun b () Bool)
(assert (> (* x (+ (- 5.0) 5.0)) (- 5.0)))
(assert b)
(check-sat)
(exit)
