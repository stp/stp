; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Every pattern but -0 written: -0 is a value of its own, whatever +0 holds,
; and its cell holds both defaults.
(set-logic QF_ABVFP)
(assert (= ((as const (Array (_ FloatingPoint 2 2) (_ BitVec 1))) #b0)
           (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store ((as const (Array (_ FloatingPoint 2 2) (_ BitVec 1))) #b1) ((_ to_fp 2 2) #x0) #b0) ((_ to_fp 2 2) #x1) #b0) ((_ to_fp 2 2) #x2) #b0) ((_ to_fp 2 2) #x3) #b0) ((_ to_fp 2 2) #x4) #b0) ((_ to_fp 2 2) #x5) #b0) ((_ to_fp 2 2) #x6) #b0) ((_ to_fp 2 2) #x7) #b0) ((_ to_fp 2 2) #x9) #b0) ((_ to_fp 2 2) #xa) #b0) ((_ to_fp 2 2) #xb) #b0) ((_ to_fp 2 2) #xc) #b0) ((_ to_fp 2 2) #xd) #b0) ((_ to_fp 2 2) #xe) #b0) ((_ to_fp 2 2) #xf) #b0)))
(check-sat)
