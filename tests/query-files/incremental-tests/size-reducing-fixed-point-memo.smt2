; The size-reducing round remembers the formulas it handed back unchanged.
; The second query is the first with its constant behind a definition that
; equality propagation substitutes away, so it reaches the round as the
; formula the first query already found to be a fixed point, and skips it.
; RUN: %solver -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(declare-fun w () (_ BitVec 32))
(push 1)
(assert (bvult (bvmul x y) (bvadd z #x00000005)))
(assert (bvult y z))
; CHECK: {sizeReducing} first round changed the formula: no
; CHECK: sat
(check-sat)
(pop 1)
(push 1)
(assert (= w #x00000005))
(assert (bvult (bvmul x y) (bvadd z w)))
(assert (bvult y z))
; CHECK: {sizeReducing} the formula is a known fixed point, skipping the round
; CHECK: sat
(check-sat)
(pop 1)
