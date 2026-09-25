; RUN: %solver --SMTLIB2 --lra-theory-propagation=1 %s | %OutputCheck %s
;
; The same machinery on a satisfiable query: a partial check that finds the
; tableau consistent must leave the search free to go on, take further bounds
; and new decision levels on top of the checked state, and accept the model
; at the end.
(set-logic QF_LRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (or p q))
(assert (=> p (and (<= (- a b) 0.0) (<= (- b c) 0.0) (<= (- c a) (- 1.0)))))
(assert (=> q (and (<= (- a b) 1.0) (<= (- b c) 1.0) (<= (- c a) 1.0) (>= a 2.0))))
; CHECK: ^sat
(check-sat)
