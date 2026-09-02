; Divide-by-zero totals through the comparator-quotient divider: quotient
; all-ones, remainder the dividend, with the divisor genuinely symbolic.
; RUN: %solver --bb.div-v5 1 %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 24))
(declare-fun b () (_ BitVec 24))
(assert (= b (_ bv0 24)))
(assert (not (and (= (bvudiv a b) (_ bv16777215 24))
                  (= (bvurem a b) a))))
(check-sat)
