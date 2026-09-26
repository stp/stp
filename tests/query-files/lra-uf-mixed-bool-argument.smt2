; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck %s
;
; A Boolean argument beside a Real one. The Boolean is read from the
; counterexample and its half of the premise is stated as an equivalence.
(set-logic QF_UFLRA)
(declare-fun g (Real Bool) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= a b))
(assert (= p q))
(assert (not (= (g a p) (g b q))))
; CHECK: rounds=2 lemmas=1
; CHECK: ^unsat
(check-sat)
