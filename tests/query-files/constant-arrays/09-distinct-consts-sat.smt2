; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Two constant arrays with different defaults are distinct.
(set-logic QF_ABV)
(assert (distinct ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01) ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x02)))
(check-sat)
