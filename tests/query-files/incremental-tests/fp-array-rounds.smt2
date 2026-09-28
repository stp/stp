; Floating point and arrays together in the incremental driver: an
; FP-element array read pinned through rounds, with the read abstraction
; and the lowering caches both persistent.
; RUN: %solver --incremental %s | %OutputCheck %s
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 8) (_ FloatingPoint 8 24)))
(declare-fun i () (_ BitVec 8))
(assert (fp.gt (select a i) (_ +zero 8 24)))
(push 1)
(assert (= i #x03))
(assert (fp.lt (select a #x03) (_ +zero 8 24)))
; a[i] > 0 with i = 3 contradicts a[3] < 0
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (distinct i #x03))
(assert (fp.lt (select a #x03) (_ +zero 8 24)))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat
(check-sat)
(exit)
