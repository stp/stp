; Per-level preparation with guarded elimination. A pushed level is
; prepared as one formula: definitions of variables PRIVATE to the level
; -- in no other live content, never bit-blasted -- are genuinely
; eliminated and recorded for model replay; everything else keeps the
; old always-asserted semantics. Three pins here:
;
; 1. Elimination + replay: x below exists only in its level; the level
;    encodes without it (the --stats line counts it) and get-value
;    answers x by evaluating its definition under the model.
; 2. Invalidation: a deeper level mentioning an eliminated variable
;    invalidates the cached preparation BEFORE anything is encoded; the
;    re-prepared level keeps the equation, so the contradiction is seen.
; 3. The freeze rule survives at level granularity: a variable that ever
;    reached the solver is never eliminated, its equation is asserted
;    and feeds the deeper levels' context.
; RUN: %solver -s --incremental --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(push 1)
(assert (= x (bvadd a #x01)))
(assert (bvult x #x0a))
; pin a so the replayed value of x is deterministic whatever phases the
; backend happens to try (the bound simplifies to a definition, so a is
; eliminated alongside x)
(assert (bvult a #x01))
; CHECK: 2 eliminated
; CHECK: ^sat
(check-sat)
; the eliminated variable answers through its definition: x = a + 1
; CHECK: \( \|a\|  #x00 \)
(get-value (a))
; CHECK: \( \|x\|  #x01 \)
(get-value (x))
(push 1)
; mentioning x invalidates the cached preparation; its equation returns,
; and x = a+1 (bounded below ten) against x = #xf0 is unsat
(assert (= x #xf0))
; CHECK: ^unsat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
(pop 1)
; freeze: bit-blast x directly, then a later level defining x must keep
; the equation asserted -- x = 5 feeding the context makes 5 > 6 unsat
(push 1)
(assert (bvult x #x0a))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x05))
(push 1)
(assert (bvugt x #x06))
; CHECK: ^unsat
(check-sat)
(pop 1)
(pop 1)
