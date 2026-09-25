; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=div -s %s 2>&1 | %OutputCheck %s
;
; Only the operations named are abstracted: with `div` alone the product is
; encoded exactly and the one quotient is the only record. The statistics
; line (-s) precedes the answer.
; CHECK: FpAbstraction: 1 abstracted
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.lt (fp.mul RNE x y) (fp.div RNE x z)))
(assert (fp.isNormal z))
(check-sat)
