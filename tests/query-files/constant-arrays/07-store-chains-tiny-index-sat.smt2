; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Over a one-bit index sort the two writes cover every cell, so two store
; chains over constant arrays with different defaults can be equal: each
; written value must be the other side's default.
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (store ((as const (Array (_ BitVec 1) (_ BitVec 8))) #x03) #b0 x) (store ((as const (Array (_ BitVec 1) (_ BitVec 8))) #x07) #b1 y)))
(assert (= x #x07))
(assert (= y #x03))
(check-sat)
