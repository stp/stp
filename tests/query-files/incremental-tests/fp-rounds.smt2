; Floating point inside the incremental driver: per-conjunct totalisation
; and lowering over one session-long encoding context, circuits reused
; across rounds.
; RUN: %solver --incremental %s | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun f () (_ FloatingPoint 8 24))
(declare-fun g () (_ FloatingPoint 8 24))
(assert (fp.gt f (_ +zero 8 24)))
(push 1)
; a positive f below 1.0 exists
(assert (fp.lt f (fp #b0 #x7f #b00000000000000000000000)))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
; and one above 8.0, doubled into g
(assert (fp.gt f (fp #b0 #x82 #b00000000000000000000000)))
(assert (= g (fp.add RNE f f)))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
; but the prefix pins f positive
(assert (fp.lt f (_ +zero 8 24)))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat
(check-sat)
; the base level can grow FP constraints between rounds
(assert (fp.lt f (fp #b0 #x81 #b00000000000000000000000)))
(push 1)
(assert (fp.gt f (fp #b0 #x82 #b00000000000000000000000)))
; f < 4.0 contradicts f > 8.0
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
