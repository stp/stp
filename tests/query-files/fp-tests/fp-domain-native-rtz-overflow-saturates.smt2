; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-domain=0 %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Under RTZ, 2546 * 79 overflows Float16 and saturates to the largest
; finite value, so p is either +0 or that value. The product's range is
; finite, but the multiplier still has to saturate: a range that is
; finite only because the mode saturates must not let the rounder drop
; its overflow handling.
(set-logic QF_FP)
(declare-fun b () Bool)
(define-fun p () (_ FloatingPoint 5 11)
  (fp.mul RTZ ((_ to_fp 5 11) RNE 2546.0)
    (ite b ((_ to_fp 5 11) RNE 79.0) (_ +zero 5 11))))
(assert (not (fp.isZero p)))
(assert (fp.lt p (fp #b0 #b11110 #b1111111111)))
(check-sat)
(exit)
