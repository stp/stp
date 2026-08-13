; Definitions asserted at PUSHED levels now rewrite the round's other
; pushed conjuncts (the defining equation always stays assumed, and the
; rewritten form is cached by its own node -- a round without the
; definition rewrites differently and never reaches the stale entry).
; Each scenario pins one way this can go wrong.
; RUN: %solver --incremental -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun p () Bool)
(assert (bvult x #xf0))
; keep y base-shared: this file pins the REWRITE-and-reuse story, so y
; must stay a real variable rather than be eliminated as level-private
; (level-elimination.smt2 pins that behaviour)
(assert (bvule y #xff))
; a definitional chain at a pushed level collapses by rewriting
(push 1)
(assert (= y #x05))
(assert (bvugt (bvadd y #x01) #x10))
; y+1 = 6 is not above 16
; CHECK: ^unsat
(check-sat)
(pop 1)
; leak pin: the popped definition must not keep rewriting
(push 1)
(assert (distinct y #x05))
; CHECK: ^sat
(check-sat)
(pop 1)
; cross-level pin: a deeper definition rewrites a shallower conjunct, and
; the rewrite dies with the deeper level
(push 1)
(assert (or (= y #x50) p))
(push 1)
(assert (= y #x50))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct y #x50))
(assert (not p))
; the disjunction still binds: y = 0x50 or p must hold
; CHECK: ^unsat
(check-sat)
(pop 1)
(pop 1)
; identical re-push reuses the rewritten encodings outright
(push 1)
(assert (= y #x05))
(assert (bvugt (bvadd y #x01) #x10))
; CHECK: Incremental: encoded 0 new conjuncts, added 0 clauses
; CHECK: ^unsat
(check-sat)
(pop 1)
; base-level protection: a pushed definition must never rewrite a
; base-level unit, whose truth is permanent
(assert (or (= x #x03) (= y #x04)))
(push 1)
(assert (= x #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct x #x03))
(assert (distinct y #x04))
; the base disjunction still binds after the pop
; CHECK: ^unsat
(check-sat)
(pop 1)
(exit)
