; The defining relation, checked through the relational encoding: quotient
; times divisor plus remainder gives the dividend back, divide-by-zero rows
; included (there the remainder is the dividend and the product term is 0).
; RUN: %solver --bb.div-by-mult 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-by-mult 1 --bb.div-lemmas 1 %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (not (= (bvadd (bvmul (bvudiv a b) b) (bvurem a b)) a)))
(check-sat)
