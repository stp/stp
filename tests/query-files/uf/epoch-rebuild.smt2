; A live UF application remains in the base while distinct pushed blocks
; accumulate and die. The tiny relief threshold forces an encoding-epoch
; rebuild; the final congruence conflict proves protected scalars, UF caches,
; and the active view were reconstructed before UFCHK.
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck --check-prefix=ANSWER %s
; RUN: %solver --uninterpreted-functions --incremental=on --incremental-reencode-limit=1 -s %s > %t 2>&1
; RUN: %OutputCheck --check-prefix=ANSWER %s < %t
; RUN: %OutputCheck --check-prefix=REBUILD %s < %t
; REBUILD-L: re-encoded from scratch
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^sat
; ANSWER: ^unsat
; ANSWER: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const base (_ BitVec 8))
(declare-const x0 (_ BitVec 8))
(declare-const x1 (_ BitVec 8))
(declare-const x2 (_ BitVec 8))
(declare-const x3 (_ BitVec 8))
(declare-const x4 (_ BitVec 8))
(declare-const x5 (_ BitVec 8))
(declare-const x6 (_ BitVec 8))
(declare-const x7 (_ BitVec 8))
(declare-const x8 (_ BitVec 8))
(declare-const x9 (_ BitVec 8))
(declare-const x10 (_ BitVec 8))
(declare-const x11 (_ BitVec 8))
(assert (= (f base) #x00))
(push 1)
(assert (bvugt (bvmul x0 x0) #x03))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x1 x1) #x27))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x2 x2) #x03))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x3 x3) #x27))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x4 x4) #x03))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x5 x5) #x27))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x6 x6) #x03))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x7 x7) #x27))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x8 x8) #x03))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x9 x9) #x27))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x10 x10) #x03))
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul x11 x11) #x27))
(check-sat)
(pop 1)
; The base UF view is still live after the epoch rotation.
(push 1)
(assert (= base x0))
(assert (distinct (f base) (f x0)))
(check-sat)
(pop 1)
(check-sat)
(exit)
