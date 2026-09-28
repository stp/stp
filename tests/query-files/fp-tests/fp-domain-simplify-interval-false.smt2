; RUN: %solver --fp-domain-simplify=1 -s %s 2>&1 | %OutputCheck %s
; CHECK: FpDomainSimplify: 1 boxed symbols, 0 interval-true, 1 interval-false
; CHECK: unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (and (fp.leq (_ +zero 8 24) x)
             (fp.leq x (fp #b0 #b10000001 #b00000000000000000000000))))
(assert (fp.gt (fp.add RNE x x)
               (fp #b0 #b10000011 #b00000000000000000000000)))
(check-sat)
