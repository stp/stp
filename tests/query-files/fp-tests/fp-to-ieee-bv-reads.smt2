; fp.to_ieee_bv, STP's extension, is read as well as printed: a float's
; packed bits, the inverse of the one-argument to_fp. The API printed it
; and the reader refused it, so a script with it did not read back.
;
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun f () (_ FloatingPoint 5 11))
(declare-fun g () (_ FloatingPoint 5 11))
(push 1)
(assert (= (fp.to_ieee_bv f) #x3c00))
(check-sat)
; CHECK: ^sat
; 0x3c00 is 1.0 in binary16
(assert (not (fp.eq f ((_ to_fp 5 11) RNE 1.0))))
(check-sat)
; CHECK-NEXT: ^unsat
(pop 1)
; the bits give the float back, whatever it is (a NaN's bits are canonical)
(assert (not (= g ((_ to_fp 5 11) (fp.to_ieee_bv g)))))
(check-sat)
; CHECK-NEXT: ^unsat
