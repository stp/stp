; c = 1.875 * 2^(1 - 2^253) at (255, 4) squares to 1.75 * 2^(3 - 2^254)
; under RNE. Constant bit propagation through the exponent arithmetic
; multiplies at more than 256 bits, where the multiplication's bounded
; enumeration once kept bit positions in bytes and answered unsat.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_FP)
(declare-fun c () (_ FloatingPoint 255 4))
(assert (= (fp.mul RNE c c) (fp #b0 (_ bv2 255) #b110)))
(check-sat)
; CHECK: ^sat
