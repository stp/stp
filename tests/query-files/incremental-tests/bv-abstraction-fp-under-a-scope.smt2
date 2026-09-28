; The floating-point route into the equality abstraction, under the
; incremental driver.
;
; Nothing here mentions a bit-vector, and the query never asks an equality:
; floating point is blasted down onto bit-vector operations, and the rounding
; modes and the packed carriers the blasting introduces are what the
; abstraction reaches once the width floor is low enough. That is a different
; way into the same congruence refinement that
; misc-tests/bv-abstraction-rounding-mode-distinct.smt2 enters directly, and
; it is the one 42 of the 383 traces of the 2026-08-18 murxla campaign took --
; filed separately, on the strength of a flag matrix that read
; --bv-term-abstraction as the culprit because turning it off suppressed the
; symptom. It suppressed it by removing the free result bits that let the
; search reach the candidate models where the bad explanation was learned; the
; defect was the explanation, in the equality abstraction, and every one of
; those traces replays clean once it is fixed.
;
; So the point of this query is the route, not a second defect: an FP query
; under a scope, with both abstractions on, which must answer sat.
; fp.rem with an infinite divisor returns the dividend, so x0 = +oo and any
; subnormal x1 satisfies it.
;
; -d re-evaluates the model against the raw assertion stack, so a wrong
; witness fails here as loudly as a wrong verdict.
;
; RUN: %solver --incremental=on -d --array-equality --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=on -d --array-equality %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
; RUN: %solver --incremental=off --array-equality --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_FP)
(declare-const x0 (_ FloatingPoint 5 11))
(declare-const x1 (_ FloatingPoint 5 11))
(push 1)
(assert (fp.isInfinite x0))
(assert (fp.isSubnormal (fp.rem x1 x0)))
(check-sat)
(pop 1)
(exit)
