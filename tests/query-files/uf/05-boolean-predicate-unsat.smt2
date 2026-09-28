; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
; EXPECT: unsat
(set-logic QF_UFBV)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(declare-fun p (Bool (_ BitVec 2)) Bool)
(assert (= b1 b2))
(assert (= x y))
(assert (p b1 x))
(assert (not (p b2 y)))
(check-sat)
