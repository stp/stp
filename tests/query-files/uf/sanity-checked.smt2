; RUN: %solver --uninterpreted-functions --check-sanity --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; MDL-07 / OBL-04: --check-sanity replays every certified model
; against the raw stack (durable applications resolved through the
; certified handle map) across a mixed sat/unsat session.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun g ((_ BitVec 8)) Bool)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (f x) #x11))
(assert (g (f x)))
(check-sat)
(push 1)
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(pop 1)
(check-sat)
