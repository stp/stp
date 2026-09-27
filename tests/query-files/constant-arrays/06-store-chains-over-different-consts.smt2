; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Two store chains over constant arrays with different defaults: the writes
; cover two of the 256 cells, so some cell holds both defaults (rule K').
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x03) #x00 x) (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) #x01 y)))
(check-sat)
