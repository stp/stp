; The comparator-quotient divider agrees with the SMT-LIB totals: a
; division identity refutable at width 24, and under the order lemmas too.
; RUN: %solver --bb.div-v5 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-v5 1 --bb.div-lemmas 1 %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 24))
(declare-fun b () (_ BitVec 24))
(assert (bvugt b (_ bv0 24)))
(assert (bvugt (bvudiv a b) a))
(check-sat)
