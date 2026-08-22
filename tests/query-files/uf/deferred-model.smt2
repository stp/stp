; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|f\|
; CHECK: \( \(\|f\| \|x\|\)  #x2A \)
; CHECK: unsupported
;
(set-logic QF_UFBV)
(set-option :produce-models true)
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
