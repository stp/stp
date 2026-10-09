; RUN: not %solver %s | %OutputCheck %s
; get-value after check-sat-assuming answers under the assumptions, and an
; unsat answer (or a stack change) invalidates the model again.
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x #x10))
; CHECK: ^sat
(check-sat-assuming ((= x #x07)))
; The model reflects the assumption that pinned x.
; CHECK: \(x #x07\)
(get-value (x))
; A fresh plain check restores a model...
; CHECK: ^sat
(check-sat)
; CHECK: \(x #x
(get-value (x))
; After an unsat answer there is no model to read.
; CHECK: ^unsat
(check-sat-assuming ((bvugt x #x20)))
; CHECK-NEXT: ^\(error "get-value is not permitted in the current solver mode"\)
(get-value (x))
(exit)
