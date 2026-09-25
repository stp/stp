; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; Bounded operands cannot overflow a product: |x|,|y| <= 8 in binary32 keeps
; e(x)+e(y) <= 6, far below emax. The abstraction proves it from the
; exponent-band rules alone, without ever encoding the multiplier.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(define-fun t () (_ FloatingPoint 8 24) (fp.mul RNE x y))
(assert (fp.leq (fp.abs x) ((_ to_fp 8 24) #x41000000)))
(assert (fp.leq (fp.abs y) ((_ to_fp 8 24) #x41000000)))
(assert (or (fp.isInfinite t) (fp.isNaN t)))
(check-sat)
