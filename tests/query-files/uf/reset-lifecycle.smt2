; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const x (_ BitVec 4))
(assert (distinct (f x) (f x)))
(check-sat)
(reset-assertions)
; The default false global-declarations policy drops f and x, permitting a
; changed signature in the same retained logic.
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (f y) (f y)))
(check-sat)
(reset)
(set-logic QF_UFBV)
(declare-fun f (Bool) Bool)
(assert (= (f true) (f true)))
(check-sat)
