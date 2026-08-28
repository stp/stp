; What a remainder is. Same story as the quotient bound: unreachable for the
; abstraction without the fact, immediate with it.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
;
; There is no exact control leg here, and there cannot be an affordable one:
; the assertion is the negation of the fact, so anything that does not install
; the fact has to prove a 256-bit divider unsatisfiable, which does not finish.
; What this leg establishes is that the fact is offered, named and applied end
; to end at a realistic width -- not that it is true. That is established by
; BVAbstractionLemma_Test, which checks every fact against the operation
; exhaustively below seven bits, by sampling at eight through sixty-four, and
; against the circuit STP blasts for the operation itself.
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (distinct b (_ bv0 256)))
(assert (bvuge (bvurem a b) b))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
