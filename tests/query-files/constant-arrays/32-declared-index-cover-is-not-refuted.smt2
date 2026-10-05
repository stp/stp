; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^sat
; A model may give S just the two elements u and v, which both writes name,
; so the equality holds in it. STP's carrier for S has more patterns than
; that, and a refutation counting them would be no refutation: the checker
; gives S the elements its terms name instead, and the model has two. The
; same block assumed again, when its lemmas are still in an incremental
; solver, is decided the same way.
(set-logic QF_AUFBV)
(declare-sort S 0)
(declare-fun u () S)
(declare-fun v () S)
(assert (distinct u v))
(push 1)
(assert (= ((as const (Array S (_ BitVec 1))) #b0) (store (store ((as const (Array S (_ BitVec 1))) #b1) u #b0) v #b0)))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= ((as const (Array S (_ BitVec 1))) #b0) (store (store ((as const (Array S (_ BitVec 1))) #b1) u #b0) v #b0)))
(check-sat)
(pop 1)
