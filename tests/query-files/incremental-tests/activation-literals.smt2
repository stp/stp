; Multi-conjunct pushed levels are assumed through one activation literal
; each -- persistent implications from the literal to the level's roots --
; so the assumption set scales with the stack depth, not the conjunct
; count, and identical level content reuses its literal and clauses.
; RUN: %solver --incremental -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (bvult x #xf0))
; three conjuncts, one assumption
(push 1)
(assert (bvult y x))
(assert (bvult z y))
(assert (bvugt z #x00))
; CHECK: assumed 1 literals
; CHECK: ^sat
(check-sat)
(pop 1)
; identical content: literal and implications reused wholesale
(push 1)
(assert (bvult y x))
(assert (bvult z y))
(assert (bvugt z #x00))
; CHECK: encoded 0 new conjuncts, added 0 clauses, assumed 1 literals
; CHECK: ^sat
(check-sat)
(pop 1)
; three levels, three assumptions
(push 1)
(assert (bvult y x))
(assert (bvugt y #x00))
(push 1)
(assert (bvult z y))
(assert (bvugt z #x00))
(push 1)
(assert (= x #x03))
; CHECK: assumed 3 literals
; y and z squeeze strictly below x = 3, so both chains still fit
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x01))
; now y < 1 and y > 0 cannot both hold
; CHECK: ^unsat
(check-sat)
(pop 1)
(pop 1)
(pop 1)
; different content at the same depth must not reuse the old literal
(push 1)
(assert (distinct y #x05))
(assert (distinct z #x06))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= y #x05))
(assert (= z #x06))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
