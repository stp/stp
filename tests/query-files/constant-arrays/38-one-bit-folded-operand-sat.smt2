; RUN: %solver --array-equality -d %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on -d %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: ( |p| true )
; The satisfiable half of 37: only p = true makes the right operand the
; all-ones array the left one folds to. The recovery's all-zeros array gave
; p = false, a model -d refuses.
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 1)))
(declare-fun e () (_ BitVec 1))
(declare-fun p () Bool)
(assert (= e #b1))
(assert (= (ite (= e #b1) ((as const (Array (_ BitVec 2) (_ BitVec 1))) #b1) a) (ite p b (store b #b01 #b0))))
(check-sat)
(get-value (p))
