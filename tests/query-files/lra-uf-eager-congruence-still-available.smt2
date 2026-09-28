; RUN: %solver --SMTLIB2 --uf-ackermann on %s | %OutputCheck %s
;
; Asking for the relation up front by name still installs it for a Real
; declaration. Laziness is what the default chooses, not the only thing the
; encoder can do, and the answer must not depend on which was chosen.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
; CHECK: ^unsat
(check-sat)
