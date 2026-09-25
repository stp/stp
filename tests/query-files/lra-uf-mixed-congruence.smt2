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
; A function over a Real and a declared sort. Its congruence used to be
; stated in full before the first solve: the Real position put it beyond the
; value-based checker, and the other position beyond the Real model. A
; committed model values both -- the arithmetic the one, the counterexample
; the other -- so the pair that breaks is found the lazy way and stated alone.
(set-logic QF_UFLRA)
(declare-sort S 0)
(declare-fun g (Real S) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun s () S)
(declare-fun t () S)
(assert (= a b))
(assert (= s t))
(assert (not (= (g a s) (g b t))))
; CHECK: rounds=2 lemmas=1
; CHECK: ^unsat
; DEFAULT: ^unsat
(check-sat)
