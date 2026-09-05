; The two-stage shift/subtract divider stays correct behind its flag: the
; quotient and remainder of a concrete division, the totalised results of a
; zero divisor, and the q*b + r identity over symbolic 8-bit operands --
; unsatisfiable only if every circuit involved is right. Both polarities run,
; so the recursive circuit answers for the same file.
;
; RUN: %solver --bb.div-v4=1 %s | %OutputCheck %s
; RUN: %solver --bb.div-v4=0 %s | %OutputCheck %s
;
; CHECK: ^unsat$
(set-logic QF_BV)
(declare-const x (_ BitVec 33))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= x (_ bv2860396893 33)))
(assert (or
  (distinct (bvudiv x (_ bv77 33)) (_ bv37148011 33))
  (distinct (bvurem x (_ bv77 33)) (_ bv46 33))
  (distinct (bvudiv x (_ bv0 33)) (_ bv8589934591 33))
  (distinct (bvurem x (_ bv0 33)) x)
  (distinct (bvadd (bvmul (bvudiv a b) b) (bvurem a b)) a)))
(check-sat)
