; RUN: %solver %s | %OutputCheck %s
;
; A RoundingMode array cell steers a rounding operation like any other
; mode term. 1 + 2^-24 falls exactly halfway between 1.0 and the next
; float up: with the cell pinned to RTP the sum rounds up to
; 1 + 2^-23, while RNE and RTZ would land on 1.0 -- so the equality below
; genuinely depends on the mode read out of the array reaching the adder.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) RoundingMode))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= (select a #b00) roundTowardPositive))
(assert (= x (fp.add (select a #b00)
                     (fp #b0 #b01111111 #b00000000000000000000000)
                     (fp #b0 #b01100111 #b00000000000000000000000))))
(assert (distinct x (fp #b0 #b01111111 #b00000000000000000000001)))
; CHECK: ^unsat
(check-sat)
