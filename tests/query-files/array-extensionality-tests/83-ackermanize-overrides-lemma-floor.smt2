; RUN: %solver --array-equality --ackermanize -s %s 2>&1 | %OutputCheck %s
; CHECK-L: after eager equality instantiation:
; CHECK: ^unsat
; --ackermanize is a request, not a hint: the block here is the same
; three-lemma one 82 declines to take unasked, and naming the flag still
; instantiates it.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 6) (_ BitVec 2)))
(declare-fun i0 () (_ BitVec 6))
(declare-fun e0 () (_ BitVec 2))
(declare-fun i1 () (_ BitVec 6))
(declare-fun e1 () (_ BitVec 2))
(declare-fun i2 () (_ BitVec 6))
(declare-fun e2 () (_ BitVec 2))
(assert (not (= i0 i1)))
(assert (not (= i0 i2)))
(assert (not (= i1 i2)))
(assert (not (= (store (store (store a i0 e0) i1 e1) i2 e2) (store (store (store a i2 e2) i1 e1) i0 e0))))
(check-sat)
