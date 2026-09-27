; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The same shape with the written value pinned away from the other side's
; default: cell 0 holds x on the left and #x07 on the right.
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (store ((as const (Array (_ BitVec 1) (_ BitVec 8))) #x03) #b0 x) (store ((as const (Array (_ BitVec 1) (_ BitVec 8))) #x07) #b1 y)))
(assert (not (= x #x07)))
(check-sat)
