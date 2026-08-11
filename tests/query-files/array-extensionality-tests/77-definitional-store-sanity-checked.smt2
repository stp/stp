; RUN: %solver --array-equality --check-sanity %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The sanity check re-evaluates the query as submitted, so reads of the
; substituted symbol and the original whole-array equality must both
; evaluate through the symbol's definition.
(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun B () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun x () (_ BitVec 4))
(declare-fun i () (_ BitVec 4))
(declare-fun y () (_ BitVec 8))
(assert (= A (store B x y)))
(assert (distinct x i))
(assert (= (select A i) (_ bv7 8)))
(assert (distinct (select B x) (select A x)))
(check-sat)
