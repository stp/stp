; A term the abstraction replaces has to be replaced exactly once, however
; many pieces the driver blasts it in.
;
; The driver prepares and encodes each conjunct of a pushed level as its own
; piece, so a subterm two conjuncts share is offered to the blaster twice.
; An abstraction is a set of fresh inputs standing for the term, constrained
; by nothing until refinement writes clauses over the record the blaster
; files; mint a second, independent set for the second ask and the two are
; free to disagree. The registry the refiner resolves a record's result
; through holds one vector per node, so the second registration hid the
; first: both records were then defined over the second set and the first
; was left unconstrained, which is an assignment the search may answer from.
; The blaster now abstracts the term once; the refiner reads each record's
; own result variables, so it does not rest on that alone.
;
; Here `t` occurs in both conjuncts and its expansion is all if-then-else,
; so the width floor of 1 abstracts it. `bvsrem 1 x` is 1 for every x except
; 1 and -1, where it is 0; no x satisfies both `t <=s x` and `t >=u x`, and
; the query is unsatisfiable at every width. With the duplicate abstraction
; live, STP answered sat -- the wrong verdict outright, not merely a model
; that fails --check-sanity.
; RUN: %solver --incremental --bv-term-abstraction=1 --bv-abstraction-width=1 %s | %OutputCheck %s
; CHECK: ^unsat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(define-fun t () (_ BitVec 4) (bvsrem (_ bv1 4) x))
(push 1)
(assert (bvsle t x))
(assert (bvuge t x))
(check-sat)
(exit)
