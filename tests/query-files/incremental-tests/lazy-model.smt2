; Deferred model construction: a sat answer does not build the
; counterexample until something reads it. -p reads it right after each
; check, so each sat is followed by the on-demand materialisation (the
; --stats line below); the values must still be the models' own. A
; session with no reader never constructs at all -- unobservable here,
; but pinned by the driver's stats staying silent about counterexample
; generation in such runs.
; RUN: %solver -s -p --incremental %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(push 1)
(assert (= x #x2a))
; CHECK: ^sat
; CHECK: materialized on demand
(check-sat)
(pop 1)
(push 1)
(assert (= x #x07))
; CHECK: ^sat
; CHECK: materialized on demand
(check-sat)
(pop 1)
