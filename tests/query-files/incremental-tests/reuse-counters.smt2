; The reuse guarantee, pinned by the driver's own counters: repeating a
; check-sat encodes nothing new, and re-pushing a formula that was seen
; before reuses its encoding entirely. --incremental engages the driver
; from the first solve, so the counters appear from the start.
; --check-sanity requests a model on each SAT result, so the frontend cannot
; answer the identical second query from its verdict cache: this test is about
; the incremental driver's counters and must actually reach that driver.
; RUN: %solver -s --incremental --check-sanity %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(push 1)
(assert (bvult x #x000000ff))
; CHECK: Incremental: encoded 1 new conjuncts
; CHECK: ^sat
(check-sat)
; the identical stack: nothing to encode, nothing to add
; CHECK: Incremental: encoded 0 new conjuncts, added 0 clauses
; CHECK: ^sat
(check-sat)
(pop 1)
; the same formula returns after a pop: still nothing new to encode
(push 1)
(assert (bvult x #x000000ff))
; CHECK: Incremental: encoded 0 new conjuncts, added 0 clauses
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
