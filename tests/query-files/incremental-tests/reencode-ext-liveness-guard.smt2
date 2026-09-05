; Each equality round extends the preceding active block. Its newly submitted
; clause delta is small, but the live block reuses the complete earlier cone.
; The relief valve's lazy full-cone guard must therefore prevent a rebuild.
; RUN: %solver --incremental --array-equality --incremental-reencode-limit 1 -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --array-equality --incremental-reencode-limit 1 -s %s 2>&1 | %OutputCheck %s
; CHECK-NOT-L: re-encoded from scratch
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun x2 () (_ BitVec 8))
(declare-fun x3 () (_ BitVec 8))
(declare-fun x4 () (_ BitVec 8))
(declare-fun x5 () (_ BitVec 8))
(declare-fun x6 () (_ BitVec 8))
(declare-fun x7 () (_ BitVec 8))

(assert (= a b))
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x0 x0) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x1 x1) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x2 x2) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x3 x3) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x4 x4) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x5 x5) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x6 x6) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(assert (bvugt (bvmul x7 x7) #x03))
; CHECK-NOT-L: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(exit)
