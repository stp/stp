; s >=u (x >> t), where t is the quotient. One of the synthesised
; inequalities: not a theorem anyone would write down, and the only thing
; standing between this query and an exact 256-bit divider.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvult b (bvlshr a (bvudiv a b))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
