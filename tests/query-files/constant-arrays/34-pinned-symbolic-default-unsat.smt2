; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=off %s | %OutputCheck %s
; CHECK-NEXT: ^unsat$
; Substitution must visit the hidden default: z is pinned to #b11, so
; overwriting one cell cannot make every other cell equal to #b00.
(set-logic QF_ABV)
(declare-fun z () (_ BitVec 2))
(assert (= ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00)
           (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) z) #b00 #b00)))
(assert (= z #b11))
(check-sat)
