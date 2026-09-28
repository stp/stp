; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
; EXPECT: unsat
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= i j))
(assert (distinct (f (select a i)) (f (select a j))))
(check-sat)
