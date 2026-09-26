; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The counterexample's term evaluator had no Real arm, so a Real term it
; walked into -- here x, reached by resolving the arguments of the Bool-sorted
; application g(x) that guards the ite -- was taken for a bit-vector and asked
; for a width it does not have. Its formula counterpart got Real arms; this is
; the term side of the same gap.
; CHECK-NEXT: ^sat$
(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun g (Real) Bool)
(declare-fun f (Real) Real)
(assert (= x (f (ite (g x) x (+ x 1.0)))))
(check-sat)
(exit)
