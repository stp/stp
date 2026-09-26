; RUN: %solver --SMTLIB2 -s --uf-propagate-equalities=0 %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 %s | %OutputCheck --check-prefix=DEFAULT %s
;
; --uf-propagate-equalities=0 is pinned because the pre-lowering pass now
; propagates this query's own equalities through the applications and
; discharges it outright, leaving no application for the lazy congruence
; loop to state a lemma about. The loop is what this file is about, so the
; first run keeps it reachable; the second checks the default path still
; reaches the same verdict without it.
;
; A Real argument and a Boolean result: the result is read from the
; counterexample and the congruence is stated as an equivalence.
(set-logic QF_UFLRA)
(declare-fun h (Real) Bool)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a b))
(assert (not (= (h a) (h b))))
; CHECK: rounds=2 lemmas=1
; CHECK: ^unsat
; DEFAULT: ^unsat
(check-sat)
