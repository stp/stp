; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_ABV)
(declare-fun v () (_ BitVec 8))
(assert (= ((as const (Array (_ BitVec 8) (_ BitVec 8))) v) ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x05)))
(assert (= v #x05))
(check-sat)
