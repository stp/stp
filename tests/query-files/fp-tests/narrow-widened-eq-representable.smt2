; RUN: %solver -d %s | %OutputCheck %s
;
; 0.5 has an exact float32 preimage, so the equality narrows to a form
; PropagateEqualities substitutes through; -d checks the model.
;
; CHECK: ^sat
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) #x3FE0000000000000)))
(assert (fp.geq x ((_ to_fp 8 24) #x3F000000)))
(check-sat)
(exit)
