; RUN: %solver --uninterpreted-functions --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|x\| .*#x01
; CHECK: define-fun \|a\| .*#x2A
; CHECK: define-fun \|f\|
; CHECK: #x7F
; CHECK: \( \(\|f\| \|x\|\)  #x7F \)
;
; Scalar, array, and UF authorities publish one certified model. The direct
; value query goes through the durable application handle, not @uf_result.
(set-option :produce-models true)
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const x (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= x #x01))
(assert (= (select a #x00) #x2a))
(assert (= (f x) #x7f))
(check-sat)
(get-model)
(get-value ((f x)))
