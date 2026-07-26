; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A consistent equality cone (a, b) side by side with an array c that
; is not connected to any equality: c stays with STP's classic lazy
; read refinement, whose congruence axiom k = l -> c[k] = c[l] is the
; only route to unsat here. Pins that cone ownership exempts exactly
; the cone -- a skip that swallowed c's reads would answer sat.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun k () (_ BitVec 4))
(declare-fun l () (_ BitVec 4))
(assert (= a b))
(assert (= (select a i) (select b i)))
(assert (= k l))
(assert (distinct (select c k) (select c l)))
(check-sat)
