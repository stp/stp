; RUN: %solver --SMTLIB2 --lra-presolve-rows=1 %s | %OutputCheck %s
;
; A row whose only variable has a zero coefficient. addLinear dropped such an
; entry when the factor cancelled against an earlier one -- x + (-x) -- but
; not when it arrived zero the first time the symbol was seen, which is what
; (* x 0) gives. The row then looked like one with a variable in it, and
; canonicalRow normalises by the leading coefficient, so it divided by zero
; and the presolve failed closed: the query lost its answer entirely.
;
; Two conjuncts, because tightenRows leaves a single one alone.
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun b () Bool)
(assert (> (* x 0.0) (- 5.0)))
(assert b)
(check-sat)
(exit)
