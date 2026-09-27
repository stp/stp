; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The same constant array written twice is one array.
(set-logic QF_ABV)
(assert (distinct ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01) ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01)))
(check-sat)
