; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
; RUN WITH: --uninterpreted-functions
; EXPECT: unsat; tuple equality is by model value, not syntax
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (distinct (f x) (f (bvadd x #x0))))
(check-sat)
