; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(define-fun h ((x (_ BitVec 8))) (_ BitVec 8) (f x))
(assert (distinct (h #x00) (h #x01)))
(check-sat) ; expected sat: distinct specializations must not alias
