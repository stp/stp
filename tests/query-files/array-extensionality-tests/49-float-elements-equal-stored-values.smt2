; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Storing =-equal float values at one index of one base gives equal
; arrays: = on floats identifies all NaNs, and the packed form a store
; writes is canonical, so value equality survives into the cells.
(set-logic QF_ABVFP)
(declare-fun base () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x y))
(assert (not (= (store base #b0 x) (store base #b0 y))))
(check-sat)
