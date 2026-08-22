; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun x1 () (_ BitVec 4))
(declare-fun x2 () Bool)
(declare-fun y1 () (_ BitVec 4))
(declare-fun y2 () Bool)
(declare-fun f ((_ BitVec 4) Bool) (_ BitVec 3))
(assert (= x1 y1))
(assert (= x2 y2))
(assert (distinct (f x1 x2) (f y1 y2)))
(check-sat)
