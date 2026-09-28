; --check-sanity is the self-check: it reads the model at solve time to
; verify it against the asserted stack, so construction stays eager --
; no on-demand materialisation may appear -- and get-value still answers
; from the already-built model.
; RUN: %solver -s --incremental --check-sanity %s 2>&1 | %OutputCheck %s
; CHECK-NOT: materialized on demand
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(push 1)
(assert (= x #x2a))
; CHECK: ^sat
(check-sat)
; CHECK: #x2A
(get-value (x))
(pop 1)
