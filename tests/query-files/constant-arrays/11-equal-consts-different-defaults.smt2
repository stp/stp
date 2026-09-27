; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; An equality between two constant arrays is an equality between their
; defaults.
(set-logic QF_ABV)
(assert (= ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x01) ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x02)))
(check-sat)
