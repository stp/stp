; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=mul,fma -s %s 2>&1 | %OutputCheck %s
;
; A fused multiply-add against the product of its own factors: with a
; non-negative addend it cannot be below the product. Both are abstracted,
; and the fact between the two records is emitted with the rules, so the
; query is unsat with neither circuit built and nothing refined.
; CHECK: FpAbstraction: 2 abstracted .* 3 cross-operation rules, .* 0 releases
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(define-fun p () (_ FloatingPoint 8 24) (fp.mul RNE x y))
(define-fun t () (_ FloatingPoint 8 24) (fp.fma RNE x y z))
(assert (fp.leq (_ +zero 8 24) z))
(assert (not (fp.isNaN p)))
(assert (not (fp.isNaN t)))
(assert (fp.lt t p))
(check-sat)
