; --uf-inject-args answers what the query asks, whatever it assumed on the way.
;
; The flag adds the converse of congruence to the eager encoding: for a
; declaration whose results are compared only with each other, results equal
; implies arguments equal. Congruence is entailed by the query. Its converse is
; not -- it says the function is injective, which the caller never wrote -- so
; the formula it strengthens the encoding into is not the query, and an unsat
; over it may be the assumption's rather than the query's. It answered exactly
; that, as `unsat`, for both of the satisfiable queries below.
;
; The asymmetry is what makes the fix cheap. An assumption only removes models,
; so a `sat` found over it is a model of the query and needs nothing done to
; it. Only an `unsat` is in question, and only when the assumption was in the
; refutation -- so every converse implication goes in behind one activation
; symbol which the search is assumed to hold, and which it can be asked about
; and made to give up. Two searches on one encoding, worst case, with every
; clause retained.
;
; So the verdicts here are the flag-off verdicts, all four of them. That is the
; whole claim, and it is why the run without the flag is checked against the
; same expectations rather than against its own.
;
; RUN: %solver --uninterpreted-functions --incremental=off --uf-inject-args=1 %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --uninterpreted-functions --incremental=on  --uf-inject-args=1 %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --uninterpreted-functions --incremental=on  %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
;
; Agreeing with the flag off is also what "the flag does nothing at all" looks
; like, and a guard nobody assumes is exactly that failure -- sound, silent,
; and worthless. So the trace is pinned too: the assumption has to be really in
; force, the refutation has to really rest on it, and it has to be really taken
; back. These runs check the same verdicts as above.
;
; RUN: %solver --uninterpreted-functions --incremental=off --uf-inject-args=1 -s %s 2>&1 | %OutputCheck --check-prefix=TRACE %s
; RUN: %solver --uninterpreted-functions --incremental=on  --uf-inject-args=1 -s %s 2>&1 | %OutputCheck --check-prefix=TRACE %s
;
; Three pairwise-distinct two-bit arguments to a function into one bit,
; asserting that two of the three results collide. That assertion is a
; tautology -- three values into two must collide -- so there is no query
; content here to be non-injective about, and injectivity contradicts it
; outright. This is the sharpest form of the wrong answer: `unsat`, definitively,
; for a query whose last line is valid.
;
; CHECK: ^sat
; CHECK: PIGEONHOLE-DONE
;
; TRACE: eager 3 of those assume injectivity
; TRACE: refutation used the injectivity assumption, retracting 3 implication\(s\)
; TRACE: ^sat
; TRACE: PIGEONHOLE-DONE
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 2)) (_ BitVec 1))
(declare-fun a () (_ BitVec 2))
(declare-fun b () (_ BitVec 2))
(declare-fun c () (_ BitVec 2))
(assert (distinct a b))
(assert (distinct b c))
(assert (distinct a c))
(assert (or (= (f a) (f b)) (= (f b) (f c)) (= (f a) (f c))))
(check-sat)
(echo "PIGEONHOLE-DONE")
;
; The query a cross-checked fuzzing campaign minimised to. Two applications
; into a one-bit codomain, so injectivity is achievable here on cardinality
; grounds and a capacity test would have let this one through: what rules the
; models out is that the query asserts the two results equal while forcing the
; arguments apart. Cardinality is not the property that makes the assumption
; safe, which is why nothing here tests for it.
;
; CHECK: ^sat
; CHECK: MINIMISED-DONE
;
; TRACE: retracting 1 implication\(s\)
; TRACE: ^sat
; TRACE: MINIMISED-DONE
(reset)
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 1))
(declare-fun g ((_ BitVec 1)) (_ BitVec 1))
(assert (= (= x (bvneg (_ bv1 1))) false))
(assert (= (g (bvneg (_ bv1 1))) (g x)))
(check-sat)
(echo "MINIMISED-DONE")
;
; A satisfiable query whose function is injective in every model of it, which
; is the shape the flag exists for. Nothing is taken back: the assumption holds
; and the first search answers. The trace pins the absence of a retraction by
; running straight from the install line to the verdict.
;
; CHECK: ^sat
; CHECK: KEPT-DONE
;
; TRACE: eager 1 of those assume injectivity
; TRACE-NOT: retracting
; TRACE: ^sat
; TRACE: KEPT-DONE
(reset)
(set-logic QF_UFBV)
(declare-fun p () (_ BitVec 4))
(declare-fun q () (_ BitVec 4))
(declare-fun h ((_ BitVec 4)) (_ BitVec 4))
(assert (distinct p q))
(assert (distinct (h p) (h q)))
(check-sat)
(echo "KEPT-DONE")
;
; An unsatisfiable query with the assumption installed over it, and
; unsatisfiable for reasons that have nothing to do with the assumption: k has
; one application, so the eager encoding has no pair to state congruence over
; and none to state its converse over either. Nothing is assumed, so nothing is
; in question and the refutation is reported as the refutation it is.
;
; CHECK: ^unsat
; CHECK: NOTHING-ASSUMED-DONE
;
; TRACE: ^unsat
; TRACE: NOTHING-ASSUMED-DONE
(reset)
(set-logic QF_UFBV)
(declare-fun r () (_ BitVec 4))
(declare-fun k ((_ BitVec 4)) (_ BitVec 4))
(assert (= (k r) (_ bv1 4)))
(assert (= (k r) (_ bv2 4)))
(check-sat)
(echo "NOTHING-ASSUMED-DONE")
