; A rounded addition of two finite target-format values has zero magnitude
; only when its exact sum is zero: a nonzero exact sum is at least one minimum
; subnormal. Thus this association-preserving row gives obj = 10*r = 50,
; contradicting the asserted upper bound 49.
;
; RUN: %solver --fp-domain-sound-zero-facts=0 --fp-domain-derived-bounds=1 --fp-domain-extremal-selectors=0 -s %s 2>&1 | %OutputCheck --check-prefix=DERIVED %s
; RUN: %solver --fp-domain-sound-zero-facts=0 -s %s 2>&1 | %OutputCheck --check-prefix=DEFAULT %s
; RUN: %solver --fp-domain-sound-zero-facts=0 --fp-domain-derived-bounds=0 --fp-domain-extremal-selectors=0 %s | %OutputCheck --check-prefix=BASE %s
; DERIVED: 1 zero-add-bounds, 1 inconsistent-boxes
; DERIVED: unsat
; DEFAULT: 1 zero-add-bounds, 1 inconsistent-boxes
; DEFAULT: unsat
; BASE: unsat

(set-logic QF_FP)
(declare-fun obj () (_ FloatingPoint 8 24))
(declare-fun r () (_ FloatingPoint 8 24))
(define-fun five () (_ FloatingPoint 8 24)
  (fp #b0 #x81 #b01000000000000000000000))
(define-fun minusTen () (_ FloatingPoint 8 24)
  (fp #b1 #x82 #b01000000000000000000000))
(define-fun fortyNine () (_ FloatingPoint 8 24)
  (fp #b0 #x84 #b10001000000000000000000))

(assert (and (fp.leq five r) (fp.leq r five)))
(assert (fp.eq
  (fp.add RNE
    (fp.add RNE (_ -zero 8 24) obj)
    (fp.mul RNE minusTen r))
  (_ +zero 8 24)))
(assert (fp.geq fortyNine obj))
(check-sat)
(exit)
