; RUN: %solver --array-equality --ackermanize %s 2>&1 | %OutputCheck %s
; CHECK-NOT-L: Warning:
; CHECK: ^unsat
; --ackermanize used to be switched off (with a warning) whenever an
; array equality was active. For plain bitvector array sorts the
; equality is now instantiated pointwise over the solve's access
; indexes and the solve stays on the eager path: no warning, and read
; congruence still propagates across the equality.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(declare-fun j () (_ BitVec 2))
(assert (= a b))
(assert (= i j))
(assert (distinct (select a i) (select b j)))
(check-sat)
