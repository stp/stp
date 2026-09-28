; Eager Ackermannisation keeps the encoded read symbols across check-sats,
; while the frontend clears the batch ArrayTransformer tables before each
; solve.  An all-cache-hit round must restore the active read observations
; before deferred model construction; otherwise the second model silently
; omits a even though its read remains asserted.
; Deliberately not run with --check-sanity: this test pins the values the model CACHE returns; --check-sanity reconstructs and can pick a different satisfying assignment.
; RUN: %solver --incremental --ackermanize -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --ackermanize --incremental-cbp-reset -s %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(assert (= (select a i) #x01))
; CHECK: ^sat
(check-sat)
; CHECK: materialized on demand
; CHECK: define-fun \|a\| .*#x01
(get-model)
; No assertion or encoding changes: this solve is entirely cache-backed.
; CHECK: ^sat
(check-sat)
; CHECK: materialized on demand
; CHECK: define-fun \|a\| .*#x01
(get-model)
(exit)
