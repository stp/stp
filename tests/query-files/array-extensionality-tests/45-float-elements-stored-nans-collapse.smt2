; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Reinterpreting two different NaN payloads gives the same NaN value,
; so storing them at the same index of the same base yields equal
; arrays.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(assert (not (= (store a #b01 ((_ to_fp 8 24) #x7FC00001))
                (store a #b01 ((_ to_fp 8 24) #xFFC00002)))))
(check-sat)
