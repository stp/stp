; A satisfiable divider pair under the lemma blocks: the side constraints
; must not exclude any real model, divide-by-zero rows included.
; RUN: %solver --bb.div-lemmas 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-lemmas 1 --bb.div-v4 1 %s | %OutputCheck %s
; CHECK: ^sat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 24))
(declare-fun b () (_ BitVec 24))
(assert (= (bvudiv a b) (_ bv16777215 24)))
(assert (= (bvurem a b) a))
(check-sat)
