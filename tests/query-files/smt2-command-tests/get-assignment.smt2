; RUN: %solver --incremental=off %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
(set-option :produce-assignments true)
; Assignment production is independent of the get-value/get-model option.
(set-option :produce-models false)
; CHECK: ^true$
(get-option :produce-assignments)
(set-logic QF_BV)
(declare-const p Bool)
(define-const ordinary Bool true)
(assert (! p :named positive))
(assert (not (! (not p) :named negative)))
(assert (= (! #x01 :named byte) #x01))
(push 1)
(assert (! true :named temporary))
; CHECK: ^sat$
(check-sat)
; CHECK-L: ((|negative| false) (|positive| true) (|temporary| true))
(get-assignment)
(pop 1)
; CHECK: ^sat$
(check-sat)
; CHECK-L: ((|negative| false) (|positive| true))
(get-assignment)
(reset-assertions)
; CHECK: ^sat$
(check-sat)
; CHECK-L: ()
(get-assignment)
(reset)
; CHECK: ^false$
(get-option :produce-assignments)
