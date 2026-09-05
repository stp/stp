; b >=u 2^k -> (a udiv b) <=u (a >> k). Taking k from the candidate
; divisor's highest set bit gives a useful quotient bound without building a
; divider. The production chooser permits at most two magnitudes per
; abstraction so a search cannot walk through the complete exponent range.
;
; Here b is in the 2^100 binade while the quotient is required to exceed
; a>>100, directly contradicting the schema.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=divisor-magnitude %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV divisor-magnitude-bound lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; There is no exact control leg here, and there cannot be an affordable one:
; the assertion is the negation of the fact, so anything that does not install
; the fact has to prove a 256-bit divider unsatisfiable, which does not finish.
; What this leg establishes is that the fact is offered, named and applied end
; to end at a realistic width -- not that it is true. That is established by
; BVAbstractionLemma_Test, which checks every fact against the operation
; exhaustively below seven bits, by sampling at eight through sixty-four, and
; against the circuit STP blasts for the operation itself.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvuge b (_ bv1267650600228229401496703205376 256)))
(assert (bvult b (_ bv2535301200456458802993406410752 256)))
(assert (bvugt (bvudiv a b) (bvlshr a (_ bv100 256))))
(check-sat)
(exit)
