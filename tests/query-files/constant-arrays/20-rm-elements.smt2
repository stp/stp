; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; RoundingMode elements: every cell of the array is the mode.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) RoundingMode))
(declare-fun i () (_ BitVec 2))
(assert (= a ((as const (Array (_ BitVec 2) RoundingMode)) RNE)))
(assert (not (= (select a i) RNE)))
(check-sat)
