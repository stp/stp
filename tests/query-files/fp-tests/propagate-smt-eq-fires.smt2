; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; SMT = over a float symbol propagates: x and y become constants, the
; fp.mul folds by construction, and every assertion is decided at the word
; level. The first RUN is the firing test -- the verdict is printed under
; --exit-after-CNF only when nothing reaches CNF generation, so this fails
; (no output) if FP_SMT_EQ propagation or the downstream constant fold
; regresses; same convention as unconstrained-fp-gt.smt2. Both literal
; spellings are covered: (fp ...) interns at parse, the to_fp reinterpret
; form is resolved by the lookthrough. The default RUN checks the model
; internally; --disable-simplifications answers through the ordinary
; blasting path with no propagation at all.
;
; 1.5 * 1.5 = 2.25 > 2.0, and 1.5 > 1.0.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun y () (_ FloatingPoint 11 53))
(assert (= x (fp #b0 #b01111111111 #b1000000000000000000000000000000000000000000000000000)))
(assert (= y ((_ to_fp 11 53) #x4000000000000000)))
(assert (fp.gt (fp.mul RNE x x) y))
(assert (fp.gt x (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))
(check-sat)
(exit)
