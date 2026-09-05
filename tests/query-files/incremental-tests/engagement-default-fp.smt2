; FP-containing logics retain the solve-3 automatic policy: their measured
; campaign benefit comes from engaging much earlier than pure BV/ABV.
; RUN: %solver -s %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun f () (_ FloatingPoint 8 24))
(push 1)

(assert (fp.gt f (_ +zero 8 24)))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)

(assert (fp.lt f (fp #b0 #x82 #b00000000000000000000000)))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)

(assert (fp.lt f (fp #b0 #x81 #b00000000000000000000000)))
; CHECK: Incremental: encoded
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
