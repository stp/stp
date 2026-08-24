; Exercise the zero-result addition rule at the underflow boundary and with a
; symbolic (but totalised) rounding mode. x + -minSub can round to zero only
; at x = minSub, so the strict upper endpoint is contradictory. The inner
; addition uses -zero to ensure the rule is numeric, not packed-zero equality.
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
(declare-fun rm () RoundingMode)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun tiny () (_ FloatingPoint 8 24))
(define-fun minSub () (_ FloatingPoint 8 24)
  (fp #b0 #x00 #b00000000000000000000001))

(assert (and (fp.leq minSub tiny) (fp.leq tiny minSub)))
(assert (fp.eq
  (fp.add rm
    (fp.add rm (_ -zero 8 24) x)
    (fp.neg tiny))
  (_ +zero 8 24)))
(assert (fp.lt x minSub))
(check-sat)
(exit)
