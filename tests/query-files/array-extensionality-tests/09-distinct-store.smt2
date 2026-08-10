; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A store at one index can differ from its base elsewhere.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(declare-fun e () (_ BitVec 2))
(assert (distinct a (store a i e)))
(check-sat)
