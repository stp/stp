; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; With distinct indices the inner write is not shadowed, so the chain
; equals the base only if read(a,j) = w as well.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= (store (store a j w) i v) a))
(assert (distinct i j))
(assert (distinct (select a j) w))
(check-sat)
