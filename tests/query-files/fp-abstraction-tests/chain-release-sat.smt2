; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; A nested chain: the inner product is an operand of the outer one through
; a proxy, so both records refine child-first and the outer release is over
; the inner surrogate, never the inner circuit.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const z (_ FloatingPoint 5 11))
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.isNormal z))
(assert (fp.lt x y))
(assert (= (fp.mul RNE (fp.mul RNE x y) z) ((_ to_fp 5 11) #x4248)))
(check-sat)
