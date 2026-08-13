; A current ordinary root can be mostly composed from cones first encoded by
; earlier, now-popped roots. Per-key submission deltas make the OR below look
; like nine live clauses even though all four multiplier cones are live. The
; lazy whole-cone guard must recover that sharing before authorizing relief.
; RUN: %solver --incremental --incremental-reencode-limit 1 -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --incremental-reencode-limit 1 -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(declare-fun x3 () (_ BitVec 8))

(push 1)
(assert (bvugt (bvmul x0 x0) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x1 x1) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x2 x2) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x3 x3) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert
  (or (bvugt (bvmul x0 x0) #x03)
      (bvugt (bvmul x1 x1) #x03)
      (bvugt (bvmul x2 x2) #x03)
      (bvugt (bvmul x3 x3) #x03)))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
; A second identical solve reaches the valve with the composite root pending.
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
