; A defining relation owns the abstraction records it carries.
;
; --bb.div-by-mult encodes each division as a relation over fresh quotient
; and remainder inputs, and the relation is asserted as a permanent unit
; rather than conjoined into any conjunct's cone. The multiplication inside
; it is wide enough to be abstracted, so the record lives where the
; per-root ownership walk cannot see it: unattributed, the scoped
; refinement treats it as dormant and certifies a candidate whose product
; the operands refute. The array equality is then true by its lowering and
; false by the cells the same model gives its operands, which the
; array-equality checker reports rather than returning the model.
;
; RUN: %solver --incremental=on --incremental-core-only --bv-term-abstraction=1 --bv-abstraction-width=8 --bb.div-by-mult=1 %s | %OutputCheck %s
(declare-const d (_ BitVec 5))
(declare-const w (_ BitVec 4))
(declare-const v (_ BitVec 15))
(declare-const a (Array (_ BitVec 6) (_ BitVec 4)))
(declare-fun q ((_ BitVec 16)) Bool)
(assert (= (store a (ite (bvslt (_ bv0 4) (bvurem (bvnot (_ bv0 4)) w)) (_ bv1 6) (_ bv0 6)) (_ bv1 4))
           (store a (_ bv0 6) (bvudiv ((_ extract 15 12) (bvudiv ((_ zero_extend 1) v) ((_ zero_extend 11) d))) w))))
; CHECK: ^sat$
(check-sat)
(assert (bvult (_ bv1 4) (ite (q (_ bv0 16)) (_ bv0 4) (_ bv3 4))))
; CHECK-NEXT: ^sat$
(check-sat)
