; The relief valve: when the persistent solver outgrows the configured
; limit and most of its encodings belong to popped, never-returning
; content, it is rebuilt from the live stack. Semantic stores survive,
; live content re-encodes through the bit-blast memo, and every answer
; before and after the rebuild must be right. The tiny limit forces the
; rebuild mid-file.
; RUN: %solver --incremental --incremental-reencode-limit 60 -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --incremental-reencode-limit 60 -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
(declare-fun e () (_ BitVec 8))
(declare-fun f () (_ BitVec 8))
(assert (bvult x #x10))
; churn: each round encodes fresh content and pops it away for good
(push 1)
(assert (bvugt (bvmul a a) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul a a) #x27))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b b) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul b b) #x27))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul c c) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul c c) #x27))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul d d) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul d d) #x27))
; by here seven dead rounds have accumulated four times the peak
; working set's clause mass: the solver restarts
; CHECK: re-encoded from scratch
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul e e) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul e e) #x27))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul f f) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul f f) #x27))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt x #x20))
; CHECK: ^unsat
(check-sat)
(pop 1)
; and correctness carries straight through the rebuild
(push 1)
(assert (= x #x05))
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
