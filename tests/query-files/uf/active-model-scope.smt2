; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^sat
; CHECK: define-fun \|f\|
; CHECK: \(ite \(= x0  #x2\)  #x22  #x00\)
; CHECK: define-fun \|unused\|
; CHECK: false
; CHECK-NOT: \(= x0  #x1\)
;
; The first solve certifies f(#x1) in a pushed block. Pop invalidates that
; seed; the second published interpretation contains only its active #x2
; observation. An active declaration with no observations is totalized by its
; deterministic false default.
(set-option :produce-models true)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(declare-fun unused (Bool) Bool)
(push 1)
(assert (= (f #x1) #x11))
(check-sat)
(pop 1)
(assert (= (f #x2) #x22))
(check-sat)
(get-model)
