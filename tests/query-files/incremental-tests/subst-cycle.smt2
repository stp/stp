; Definitions that are innocent alone and cyclic together: each passes
; the occurs-check against its RAW replacement, but expanding one through
; the other yields a self-referential entry, and replace() diverges on it
; (stack overflow). The harvest must re-run the occurs-check on the
; EXPANDED replacement and refuse the entry; the equation itself is still
; asserted, so refusing only costs rewriting. All three cyclic shapes
; below crashed before that check existed.
; RUN: %solver --incremental %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 %s | %OutputCheck %s
(set-logic QF_BV)
; a pushed definition against a base one: base b = k+1, pushed k = b
; composes to k -> k+1 in the merged map
(declare-fun k () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (= b (bvadd k (_ bv1 32))))
(push 1)
(assert (= k b))
; a conjunct that consumes the merged map: rewriting it walks the
; k -> b -> k+1 cycle
(assert (bvult k (_ bv100 32)))
; k = k + 1 has no solution
; CHECK: ^unsat
(check-sat)
(pop 1)
; the cycle popped away; the base alone is satisfiable
; CHECK: ^sat
(check-sat)
; a SATISFIABLE base-level cycle: a -> m & 0xff, then m = a expands to
; m -> (m & 0xff) | 0x0f -- refusing the entry must not disturb the
; verdict
(declare-fun m () (_ BitVec 32))
(declare-fun a () (_ BitVec 32))
(assert (= a (bvand m (_ bv255 32))))
(assert (= m (bvor a (_ bv15 32))))
; CHECK: ^sat
(check-sat)
; and an UNSATISFIABLE base-level cycle (the original reproducer):
; x -> bvurem(1, y), then y = x expands to y -> bvurem(1, y)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= x (bvurem (_ bv1 32) y)))
(assert (not (distinct x y)))
; CHECK: ^unsat
(check-sat)
