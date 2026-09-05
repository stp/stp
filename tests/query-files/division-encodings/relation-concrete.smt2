; A concrete quotient/remainder pair through the relational encoding, with
; one symbolic operand so the relation is not constant-folded away.
; RUN: %solver --bb.div-by-mult 1 %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(assert (= a (_ bv50000 16)))
(assert (not (and (= (bvudiv a (_ bv7 16)) (_ bv7142 16))
                  (= (bvurem a (_ bv7 16)) (_ bv6 16)))))
(check-sat)
