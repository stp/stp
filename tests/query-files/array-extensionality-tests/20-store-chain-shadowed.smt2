; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The inner write at the identical index is shadowed by the outer one,
; so w is unconstrained: only read(a,i) = v is forced.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= (store (store a i w) i v) a))
(assert (distinct (select a i) w))
(check-sat)
