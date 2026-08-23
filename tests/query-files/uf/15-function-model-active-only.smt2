; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|f\|
; CHECK: \(ite \(= x0  #x1\)  #x2A \(ite \(= x0  #x2\)  #x7F  #x00\)\)
;
; RUN WITH: --uninterpreted-functions
; EXPECT: sat and replayable deterministic nested-ite model for f
(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (= x #x1))
(assert (= y #x2))
(assert (= (f x) #x2a))
(assert (= (f y) #x7f))
(check-sat)
(get-model)
