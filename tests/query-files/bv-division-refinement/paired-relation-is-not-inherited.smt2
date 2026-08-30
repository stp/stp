; The paired quotient/remainder recomposition identity builds a full-width
; multiplier, so it is not part of the mask an enabled abstraction inherits.
; The query below is decided by that relation alone -- q=2 and r=1 require
; low(a) = low(2b+1), which is 1 where the assertions force it to 0 -- so
; asking for the group makes the lemma fire, and not asking for it has to
; reach the same answer the long way. Fixing q and r to nonzero values also
; keeps both operations live through preprocessing.
; The schema below is chosen off the first candidate model, which rides on
; the CNF: the rung is pinned so a backend or compiler change cannot move it.
; RUN: %solver --incremental=off -s --cnf-generation-effort=medium --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=base,divrem-full %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --cnf-generation-effort=medium --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 %s 2>&1 | %OutputCheck %s --check-prefix=INHERITED
; CHECK: BV abstraction: paired BVDIV/BVMOD recomposition lemma over 256 bits
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
; INHERITED-NOT: paired BVDIV/BVMOD recomposition
; INHERITED: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= (bvudiv a b) (_ bv2 256)))
(assert (= (bvurem a b) (_ bv1 256)))
(assert (= ((_ extract 2 0) a) #b000))
(assert (= ((_ extract 2 0) b) #b000))
(check-sat)
(exit)
