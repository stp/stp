; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (distinct (let ((x #x00)) (f x)) (f #x00)))
(assert (= (let ((x #x01)) (let ((x #x00)) (f x))) (f #x00)))
(check-sat) ; expected unsat
