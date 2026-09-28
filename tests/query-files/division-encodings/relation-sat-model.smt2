; The relational encoding must not exclude any real model: the
; divide-by-zero row is satisfiable, with the quotient totalised to
; all-ones and the remainder to the dividend.
; RUN: %solver --bb.div-by-mult 1 %s | %OutputCheck %s
; CHECK: ^sat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 24))
(declare-fun b () (_ BitVec 24))
(assert (= (bvudiv a b) (_ bv16777215 24)))
(assert (= (bvurem a b) a))
(check-sat)
