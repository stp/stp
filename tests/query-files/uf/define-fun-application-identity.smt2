; Instantiating a define-fun whose body is a UF application must recover the
; same durable application identity as spelling that application directly.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^unsat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(define-fun h ((x (_ BitVec 8))) (_ BitVec 8) (f x))
(declare-const a (_ BitVec 8))
(assert (distinct (h a) (f a)))
(check-sat)
