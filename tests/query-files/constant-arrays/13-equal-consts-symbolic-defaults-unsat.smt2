; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; With symbolic defaults the equality of the arrays is the equality of the
; defaults.
(set-logic QF_ABV)
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= ((as const (Array (_ BitVec 8) (_ BitVec 8))) v) ((as const (Array (_ BitVec 8) (_ BitVec 8))) w)))
(assert (not (= v w)))
(check-sat)
