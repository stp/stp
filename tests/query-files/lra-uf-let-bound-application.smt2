; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A let bound to an application. Naming it asks the node what sort it is,
; which every application answers with the same kind -- so the answer has to
; come from the sort it was built at, or the name is taken for a formula and
; the term position it appears in is a syntax error.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (let ((t (f x))) (> t 1.0)))
; CHECK: ^sat
(check-sat)
