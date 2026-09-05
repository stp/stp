; Whole-array equality encodes each active stack as one block. Churn below
; leaves those complete blocks behind, so the relief valve must account for
; their retained clauses and eventually rebuild. The final equality conflict
; checks refinement correctness across that rebuild.
; RUN: %solver --incremental --array-equality --incremental-reencode-limit 1 -s %s > %t 2>&1
; RUN: %solver --incremental-auto-engage-at 1 --array-equality --incremental-reencode-limit 1 -s %s > %t 2>&1
; RUN: %OutputCheck %s < %t
; RUN: %OutputCheck --check-prefix=REBUILD %s < %t
; REBUILD-L: re-encoded from scratch
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
(declare-fun x8 () (_ BitVec 8))
(declare-fun x9 () (_ BitVec 8))
(declare-fun x10 () (_ BitVec 8))
(declare-fun x11 () (_ BitVec 8))

(push 1)
(assert (= a b))
(assert (bvugt (bvmul x0 x0) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x1 x1) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x2 x2) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x3 x3) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x4 x4) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x5 x5) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x6 x6) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x7 x7) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x8 x8) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x9 x9) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x10 x10) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= a b))
(assert (bvugt (bvmul x11 x11) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (= a b))
(assert (= (select a #x1) #x11))
(assert (= (select b #x1) #x22))
; CHECK: ^unsat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
(exit)
