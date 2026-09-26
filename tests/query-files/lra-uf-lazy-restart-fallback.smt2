; RUN: %solver --SMTLIB2 -s --uf-lazy-in-place=0 --uf-propagate-equalities=0 %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 --uf-lazy-in-place=0 %s | %OutputCheck --check-prefix=DEFAULT %s
;
; --uf-propagate-equalities=0 is pinned because the pre-lowering pass now
; propagates this query's own equalities through the applications and
; discharges it outright, leaving no application for the lazy congruence
; loop to state a lemma about. The loop is what this file is about, so the
; first run keeps it reachable; the second checks the default path still
; reaches the same verdict without it.
;
; The fallback. A lazy round normally extends the running solve in place;
; when it cannot -- the theory propagator holds the context, or, as here, the
; switch is off -- the lemmas earned are stated over a new solve of the query
; from the top. Same lemmas, same answer, one restart.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
; CHECK: rounds=2 lemmas=1 expanded=0 restarts=1
; CHECK: ^unsat
; DEFAULT: ^unsat
(check-sat)
