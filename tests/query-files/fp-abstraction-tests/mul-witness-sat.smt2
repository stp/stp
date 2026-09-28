; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; A product pinned to a constant needs the exact value: the rules bound it,
; a value lemma or the exact release finds it, and the answer is checked
; against the exact semantics before it is reported.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.lt x y))
(assert (= (fp.mul RNE x y) ((_ to_fp 5 11) #x4248)))
(check-sat)
