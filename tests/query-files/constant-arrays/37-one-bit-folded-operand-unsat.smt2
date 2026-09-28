; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; With e = #b1 the equality's left operand is the constant array of #b1, and
; its witness read folds to "name = #b1" -- which the simplifier writes, for
; a one-bit name, as (not (= #b0 name)). The operand recovery took the
; equation inside the NOT for a fact and recovered the constant array of #b0,
; so the equality was checked against the wrong array: sat, where the store
; of #b0 at #b01 makes the right operand differ from all-ones once p is
; false.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 1)))
(declare-fun e () (_ BitVec 1))
(declare-fun p () Bool)
(assert (= e #b1))
(assert (= (ite (= e #b1) ((as const (Array (_ BitVec 2) (_ BitVec 1))) #b1) a) (ite p b (store b #b01 #b0))))
(assert (not p))
(check-sat)
