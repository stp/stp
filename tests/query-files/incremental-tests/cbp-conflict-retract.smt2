; A level the constant-bit engine refutes against the live prefix is
; answered unsat by asserting FALSE at that level -- and the refuting
; feed still mutated the engine, so the level MUST be recorded as fed:
; an unrecorded refutation survives the level's pop unnoticed (the
; divergence check compares only recorded feeds) and the engine's
; latched conflict then refutes whatever level is pushed in its place.
; The pop below re-pushes consistent content and must come back sat;
; re-pushing the contradiction later must derive the conflict again. (The
; intervening replacement trimmed that suffix's memo entry.)
; RUN: %solver --incremental --check-sanity -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --check-sanity -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --incremental-cbp-reset --check-sanity -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun flag () Bool)
(declare-fun x () (_ BitVec 8))
(push 1)
; Pins flag=true through the transfer functions.
(assert (= (bvand (ite flag #x01 #x02) #x03) #x01))
(push 1)
; Bit-level contradiction with the pinned flag: the feed conflicts and
; FALSE is asserted at this level.
(assert (not flag))
; CHECK: ^unsat
(check-sat)
(pop 1)
(push 1)
; Consistent replacement at the same depth: a leaked conflict would
; refute this too.
(assert flag)
(assert (= x #x2A))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
; Re-push of the refuted content after an intervening replacement: the
; replacement trimmed this suffix's memo, so CBP derives the conflict again.
(assert (not flag))
; CHECK: ^unsat
(check-sat)
(pop 1)
(pop 1)
; The pinning level itself is gone: (not flag) alone is satisfiable.
(push 1)
(assert (not flag))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
