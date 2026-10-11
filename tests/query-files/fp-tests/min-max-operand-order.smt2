; RUN: %solver %s | %OutputCheck %s
;
; fp.min and fp.max are unspecified on (+0, -0) and (-0, +0), independently
; of each other, so with two symbols the two operand orders are two
; applications that may disagree: the first query is sat. With a non-zero
; constant on one side the pair of zeros is impossible, the operation is
; commutative, and the factory builds both orders as one node: the second
; query is unsat.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 3 5))
(declare-fun y () (_ FloatingPoint 3 5))
(define-fun one () (_ FloatingPoint 3 5) ((_ to_fp 3 5) RNE 1.0))
(push 1)
(assert (not (= (fp.min x y) (fp.min y x))))
; CHECK: ^sat$
(check-sat)
(pop 1)
(push 1)
(assert (or (not (= (fp.min x one) (fp.min one x)))
            (not (= (fp.max x one) (fp.max one x)))))
; CHECK-NEXT: ^unsat$
(check-sat)
(pop 1)
(exit)
