; --fp-abstraction-budget releases every remaining record, spliced in
; place, at the first candidate check past the budget. Whether the budget
; fires here depends on the machine; either way the answer is the
; default abstraction's, which is what this pins.
;
; RUN: %solver --fp-abstraction=true --fp-abstraction-budget=1 %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-budget=1000 %s | %OutputCheck %s
; CHECK: ^sat$
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun y () (_ FloatingPoint 11 53))
(declare-fun z () (_ FloatingPoint 11 53))
(assert (fp.gt (fp.mul RNE x y) (fp.div RNE z x)))
(assert (fp.lt (fp.mul RNE x y) (fp.mul RNE z z)))
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.isNormal z))
(check-sat)
(exit)
