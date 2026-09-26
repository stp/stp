; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A Boolean-valued function with no Real anywhere in its signature, in a
; query that has Real arithmetic elsewhere. The model replay evaluates the
; whole public root, and the evaluator cannot value a Real predicate: it used
; to walk into this one and ask it for a bit width. Real syntax anywhere in
; the root is the arithmetic's to check, and the replay stands aside.
(set-logic QF_UFLRA)
(declare-sort S 0)
(declare-fun f (S) Bool)
(declare-fun v () Real)
(declare-fun s () S)
(assert (f s))
(assert (= v 0.0))
; CHECK: ^sat
(check-sat)
