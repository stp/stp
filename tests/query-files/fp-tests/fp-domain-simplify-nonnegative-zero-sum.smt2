; RUN: %solver --fp-domain-simplify=1 -s %s 2>&1 | %OutputCheck %s
; CHECK: FpDomainSimplify: 2 boxed symbols, 0 interval-true, 0 interval-false, 0 classifier-false, 0 diff-zero-eq, 1 nonnegative-zero-sum
; CHECK: sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (and (fp.leq (_ +zero 8 24) x)
             (fp.leq x (fp #b0 #b10000001 #b00000000000000000000000))
             (fp.leq (_ +zero 8 24) y)
             (fp.leq y (fp #b0 #b10000001 #b00000000000000000000000))
             (fp.eq (fp.add RNE x y) (_ +zero 8 24))))
(check-sat)
