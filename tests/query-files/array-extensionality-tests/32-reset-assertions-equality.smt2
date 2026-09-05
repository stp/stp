; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; With the default :global-declarations false, reset-assertions drops both
; the asserted equality and the declarations. Redeclaring the arrays starts
; a fresh equality scope, and the two new arrays may differ.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (= a b))
(assert (distinct (select a #b00) (select b #b00)))
(check-sat)
(reset-assertions)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (distinct (select a #b01) (select b #b01)))
(check-sat)
