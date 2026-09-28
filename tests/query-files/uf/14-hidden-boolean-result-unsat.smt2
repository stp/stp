; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
; RUN WITH: --uninterpreted-functions (release build)
; EXPECT: unsat; hidden Boolean inner results must each have one SAT variable
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun p ((_ BitVec 4)) Bool)
(declare-fun f (Bool) (_ BitVec 3))
(assert (= x y))
(assert (distinct (f (p x)) (f (p y))))
(check-sat)
