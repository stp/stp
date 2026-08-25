; REQUIRES: cadical
;
; The pass reads what the SAT backend fixed at the root while simplifying,
; and CaDiCaL is the only backend that reports that. Everywhere else it is a
; sound no-op -- it derives nothing rather than deriving something wrong --
; so there is nothing for this to observe.
;
; The skeleton pass exists to notice what the connectives settle without
; blasting anything. Here a fact follows only by chaining two implications
; over predicates it treats as opaque, which is exactly the shape
; PropagateEqualities cannot take -- it handles a bare Boolean symbol, an
; equality and a two-argument XOR, and an implication is none of those.
;
; The count is checked loosely: what matters is that the structure was
; consulted and settled something, not how many facts a given SAT backend
; happens to fix while simplifying.
; RUN: %solver -s --skeleton-preproc=1 %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(assert (bvult x y))
(assert (=> (bvult x y) (bvult y z)))
(assert (=> (bvult y z) (= x (_ bv7 32))))
(assert (distinct z (_ bv0 32)))
; CHECK: Skeleton preprocessing: [0-9]+ nodes, [0-9]+ atoms, [1-9][0-9]* forced
; CHECK: ^sat
(check-sat)
(exit)
