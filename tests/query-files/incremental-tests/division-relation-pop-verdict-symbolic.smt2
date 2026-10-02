; RUN: %solver --incremental=on --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-mult=1 %s | %OutputCheck %s
; RUN: %solver --incremental=on --ackermanize --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-mult=1 %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at=1 -d --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-mult=1 %s | %OutputCheck %s
; RUN: %solver -d --bv-eq-abstraction=1 --bv-abstraction-width=8 --bb.div-by-mult=1 %s | %OutputCheck %s
;
; division-relation-pop-verdict.smt2 with a symbolic divisor: the relation
; x = d*q + r is the other encoding that mints a quotient-remainder pair.
; After the pop the second level's refined equality was over the first
; level's free pair and the query answered sat; with d nonzero, x / d is
; never above x.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (bvugt d #x00))
(push 1)
(assert (= (bvand y v) (bvudiv x d)))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (bvand z w) (bvudiv x d)))
(assert (bvugt (bvand z w) x))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
