; The q <= a order law: a quotient strictly above its dividend needs a zero
; divisor, and a zero divisor forces the all-ones quotient; leaving one
; quotient bit clear refutes both branches.
; RUN: %solver --bb.div-lemmas 1 %s | %OutputCheck %s
; RUN: %solver --bb.div-lemmas 1 --bb.div-v4 1 %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 24))
(declare-fun b () (_ BitVec 24))
(assert (bvugt (bvudiv a b) a))
(assert (= ((_ extract 5 5) (bvudiv a b)) (_ bv0 1)))
(check-sat)
