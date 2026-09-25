; RUN: %solver --SMTLIB2 -s --uf-lazy-round-limit=1 --uf-lazy-full-expansion-pairs=0 --uf-congruence-closure=off %s 2>&1 | %OutputCheck --check-prefix=OFF %s
; RUN: %solver --SMTLIB2 -s --uf-lazy-round-limit=1 --uf-lazy-full-expansion-pairs=0 --uf-congruence-closure=on %s 2>&1 | %OutputCheck --check-prefix=ON %s
;
; The congruence-closure escalation, and that it does not change the answer.
;
; With a = b, congruence forces (g a) = (g b) and then (f (g a)) = (f (g b));
; the last assertion denies the latter, so the query is unsat. c = d also
; gives f a direct pair it can break before the nested equality propagates:
; (f c) and (f d) stand at one point but may have different candidate values.
; The flags force escalation: the round limit is one, and the full-expansion
; gate is zero, so no function is Ackermannised and a broken one that is
; "too large" (any with a pair, here) escalates.
;
; The value-grouping path may need one re-solve per layer of nesting. Closure
; can state the nested pair in the round it escalates f, but which function
; breaks first depends on the arithmetic driver's candidate model. Require
; unsat within two refinement rounds, at most the seven possible pairs, and
; escalation only when enabled. UFLowering.LazyClosurePredictsNestedPair
; checks the predictive lemma on a fixed candidate rather than relying on
; either driver's model selection to demonstrate the saved round.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(assert (= a b))
(assert (= c d))
(assert (> (+ (f c) (f d)) 0.0))
(assert (not (= (f (g a)) (f (g b)))))
; OFF: rounds=[23] lemmas=[1-7] expanded=0 restarts=0
; OFF: ^unsat
; ON: rounds=[23] lemmas=[1-7] expanded=[12] restarts=0
; ON: ^unsat
(check-sat)
