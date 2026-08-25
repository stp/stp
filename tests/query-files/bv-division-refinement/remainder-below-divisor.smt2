; What a remainder is. Same story as the quotient bound: unreachable for the
; abstraction without the fact, immediate with it.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (distinct b (_ bv0 256)))
(assert (bvuge (bvurem a b) b))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
