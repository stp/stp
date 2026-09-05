; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(assert (= x y))
(assert (distinct (f (g x)) (f (g y))))
(check-sat)
