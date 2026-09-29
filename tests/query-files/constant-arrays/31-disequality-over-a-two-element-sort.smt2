; RUN: %solver --array-equality --uf-sort-width 1 %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A declared sort of two carriers, one written: the other's cell differs.
(set-logic QF_AUFBV)
(declare-sort S 0)
(declare-fun u () S)
(assert (not (= ((as const (Array S (_ BitVec 1))) #b0)
                (store ((as const (Array S (_ BitVec 1))) #b1) u #b0))))
(check-sat)
