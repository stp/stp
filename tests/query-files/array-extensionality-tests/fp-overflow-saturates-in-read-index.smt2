; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Reduced from a fuzzer failure. The read index converts an RTZ product
; that overflows Float16 and saturates. When the native multiplier lost
; that saturation, the SAT assignment disagreed with the model's value of
; the index, and the array-equality checker stopped with "a scalar name
; disagrees with its term".
(set-logic QF_ABVFP)
(declare-fun r () RoundingMode)
(declare-fun i () Float32)
(declare-fun a () (Array (_ BitVec 5) Float32))
(declare-fun x () (Array Float32 Float128))
(declare-fun y () (Array Float32 Float128))
(define-fun p () (_ FloatingPoint 5 11)
  (fp.mul RTZ ((_ to_fp 5 11) RNE 2546.0)
    (ite (fp.isZero ((_ to_fp 5 11) r (_ +zero 8 24)))
         ((_ to_fp 5 11) RNE 79.0)
         (_ +zero 5 11))))
(assert (ite (distinct x y (store x i (select x (select a #b00000))))
             false
             (fp.isNaN (select a ((_ extract 5 1) ((_ fp.to_ubv 6) RTZ p))))))
(check-sat)
(exit)
