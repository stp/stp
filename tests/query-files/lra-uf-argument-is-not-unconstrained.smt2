; RUN: %solver --SMTLIB2 --lra-presolve-unconstrained=1 %s | %OutputCheck %s
;
; x is handed straight to f as an argument, so the lowering uses it directly
; and it stays a user variable -- an introduced-symbol test does not catch it.
; It is no freer than a result symbol: congruence relates two applications by
; the values of their arguments, so pinning x decides whether f(x) and f(f(x))
; must agree. Witnessing it made this sat query unsat. The stage now steps
; aside for any query carrying a UF context at all, which covers arguments and
; result symbols alike; this pins the answer rather than the mechanism.
;
; sat with, e.g., f(y) = y - 1: x >= x-1, and x-2 < x-1.
; CHECK-NEXT: ^sat$
(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun f (Real) Real)
(assert (>= x (f x)))
(assert (< (f (f x)) (f x)))
(check-sat)
(exit)
