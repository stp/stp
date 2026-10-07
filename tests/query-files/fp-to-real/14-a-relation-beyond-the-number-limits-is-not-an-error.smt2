; RUN: %solver %s | %OutputCheck %s
; At exponent width 16 the constants of fp.to_real fit the exact arithmetic's
; number limits, but relating two conversions can need more than they allow.
; A solve that runs into them stops, which is an unknown answer with its
; reason rather than an error (it was SOLVER_ERROR, "Fatal Error" and exit
; 255), whether the SAT backend hands the arithmetic each assignment during
; its search or a whole candidate at a time. Whether this one does is the
; search's doing: NaN and the infinities convert to Real constants of their
; own, and a search that tries them -- MiniSat's, with the theory taking part
; -- answers sat without relating two conversions at all. So either answer is
; right here, and an error is not; the API test of the same name checks the
; reason whenever the answer is unknown.
; CHECK-NEXT: ^(unknown|sat)$
; The solver goes on. (Whether a check over a single conversion stays within
; the limits at this width depends on the backend, so none is made here.)
; CHECK-NEXT: ^sat$
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 16 3))
(declare-fun y () (_ FloatingPoint 16 3))
(push 1)
(assert (< (fp.to_real x) (fp.to_real y)))
(check-sat)
(pop 1)
(assert (fp.isZero x))
(check-sat)
