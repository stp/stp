; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; reset-assertions drops the asserted equality; the record it minted
; stays registered, and the second solve re-conjoins its (conservative)
; witness bundle. The two arrays may then differ again.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (= a b))
(assert (distinct (select a #b00) (select b #b00)))
(check-sat)
(reset-assertions)
(assert (distinct (select a #b01) (select b #b01)))
(check-sat)
