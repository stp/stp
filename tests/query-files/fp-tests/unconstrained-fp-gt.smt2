; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
;
; An unconstrained float compared against an ordinary constant is eliminated
; before the comparison is ever blasted: RemoveUnconstrained replaces the
; fp.gt with a fresh boolean and records x := ite(v, +oo, NaN), so the solve
; never builds the unpack circuit.
;
; --exit-after-CNF makes this a test that the elimination actually FIRES,
; not merely that the answer is right: every assertion here collapses at the
; word level, so the sat is decided before CNF generation and printed even
; though the run stops there. If the rule regresses, the comparisons reach
; the bit-blaster, the run exits at the CNF with no verdict, and the CHECK
; fails. (Same convention as simplification-tests/.) Both literal spellings of the constant
; must work: (fp ...) literals intern as constants at parse, while
; ((_ to_fp e s) bits) stays a reinterpret term that the rule resolves
; itself.
;
; The two constants here are 1.3 (binary64) spelled both ways; both asserts
; are satisfied by x = +oo, y = +oo.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun y () (_ FloatingPoint 11 53))
(assert (fp.gt x ((_ to_fp 11 53) #x3FF4CCCCCCCCCCCD)))
(assert (fp.gt y (fp #b0 #b01111111111 #b0100110011001100110011001100110011001100110011001101)))
; Both sides unconstrained: eliminated with the witness pair (+oo, +0).
(declare-fun z () (_ FloatingPoint 11 53))
(declare-fun w () (_ FloatingPoint 11 53))
(assert (fp.gt z w))
(check-sat)
(exit)
