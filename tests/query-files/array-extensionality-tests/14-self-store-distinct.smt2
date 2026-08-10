; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Writing back the value already present yields the same array.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(assert (distinct (store a i (select a i)) a))
(check-sat)
