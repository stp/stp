; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The two arrays differ at index #b1. With one-bit cells the witness of the
; disequality is pinned to a value, and bit propagation must leave the
; witness read inside the equation it is anchored by.
(set-logic QF_ABV)
(assert (not (= ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b0)
                (store ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b1) #b0 #b0))))
(check-sat)
