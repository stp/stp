; produce-models asks for models to be READABLE, not verified: it feeds
; the construction derivations, never the self-check flag, and the driver
; defers construction to the first reader. Each get-value below is what
; triggers materialisation (the --stats lines), and the values must be
; the models' own.
; Deliberately not run with --check-sanity: this test exists to check that a model is built only when asked; --check-sanity always asks.
; RUN: %solver -s --incremental %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(push 1)
(assert (= x #x2a))
; CHECK: ^sat
(check-sat)
; CHECK: materialized on demand
; CHECK: #x2A
(get-value (x))
(pop 1)
(push 1)
(assert (= x #x07))
; CHECK: ^sat
(check-sat)
; CHECK: materialized on demand
; CHECK: #x07
(get-value (x))
(pop 1)
