; A mostly-LIVE encoding must never trip the relief valve, however far
; past the size floor it grows: a rebuild only pays when most clause
; mass belongs to popped, never-returning content. Every round here
; re-pushes the SAME conjunct -- its encoding is reused, so it IS the
; working set -- and the base only grows, so the deadness ratio never
; holds. The size floor is set absurdly low to prove the mass ratio is
; what does the protecting.
; RUN: %solver -s --incremental --incremental-reencode-limit 60 %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 --incremental-reencode-limit 60 %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (bvult (bvmul x x) #xf0))
(push 1)
(assert (bvugt (bvmul y y) #x03))
; CHECK-NOT: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y y) #x03))
; CHECK-NOT: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(assert (bvult x #xf0))
(push 1)
(assert (bvugt (bvmul y y) #x03))
; CHECK-NOT: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y y) #x03))
; CHECK-NOT: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(assert (bvult y #xf1))
(push 1)
(assert (bvugt (bvmul y y) #x03))
; CHECK-NOT: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y y) #x03))
; CHECK-NOT: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
