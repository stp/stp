; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The value classes are DISJOINT: no operand is both zero and subnormal, or
; both NaN and infinite (the significand field is zero in one and nonzero in
; the other), or both normal and infinite (the exponent field is all-ones in
; one and not in the other). Fresh symbols per pair, ored together, so any
; one overlap makes the formula sat. This is the half of the partition that
; catches a class test that drops one of its two field conditions -- an
; isNormal encoded as just "exponent nonzero", or an isInfinite that ignores
; the significand and so swallows the NaNs
; (native-classify-partition.smt2 is the cover half, and a cover test cannot
; see either mistake).
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(declare-fun w () (_ FloatingPoint 8 24))
(assert (or (and (fp.isZero y) (fp.isSubnormal y))
            (or (and (fp.isNormal z) (fp.isInfinite z))
                (and (fp.isNaN w) (fp.isInfinite w)))))
(check-sat)
(exit)
