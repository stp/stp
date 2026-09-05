; Floating-point models from the incremental driver: get-value answers
; through the session-long encoding context, and pinned values round-trip
; bit for bit.
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BVFP)
(declare-fun f () (_ FloatingPoint 8 24))
(assert (fp.gt f (_ +zero 8 24)))
(push 1)
(assert (= f (fp #b0 #x80 #b10000000000000000000000)))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \|f\| +\(fp #b0 #b10000000 #b10000000000000000000000\)
(get-value (f))
(pop 1)
(push 1)
(assert (= f (fp #b0 #x7f #b00000000000000000000000)))
; CHECK: ^sat
(check-sat)
; CHECK: \|f\| +\(fp #b0 #b01111111 #b00000000000000000000000\)
(get-value (f))
(pop 1)
; after the pop the model is stale, per SMT-LIB
; CHECK: ^unsupported
(get-value (f))
(exit)
