; RUN: %solver %s | %OutputCheck %s
; At exponent width 16 the constants of fp.to_real fit the exact arithmetic's
; number limits, but relating two conversions needs more than they allow. The
; solve stops at the limit, which is an unknown answer with its reason rather
; than an error (it was SOLVER_ERROR, "Fatal Error" and exit 255).
; CHECK-NEXT: ^unknown$
; CHECK-NEXT-L: (:reason-unknown (incomplete "the exact linear arithmetic solver could not decide this query within its number limits"))
; A single conversion against a constant still decides.
; CHECK-NEXT: ^sat$
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 16 3))
(declare-fun y () (_ FloatingPoint 16 3))
(push 1)
(assert (< (fp.to_real x) (fp.to_real y)))
(check-sat)
(get-info :reason-unknown)
(pop 1)
(assert (= (fp.to_real x) 2.0))
(check-sat)
