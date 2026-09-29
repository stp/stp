; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|f\|
; CHECK: \( \(\|f\| \|x\|\)  #x2A \)
; CHECK: error "get-value is not permitted
;
(set-option :produce-models true)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #x2a))
(check-sat)
(get-model)
(get-value ((f x)))
(push 1)
(assert (distinct x x))
(get-value ((f x)))
(pop 1)
