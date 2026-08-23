; RUN: %solver -d %s | %OutputCheck %s
;
; The satisfiable side of the same boundary: the float32 just BELOW the
; float64 0.1 satisfies both conjuncts; -d checks the model.
;
; CHECK: ^sat
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.lt ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) #x3FB999999999999A)))
(assert (fp.geq x ((_ to_fp 8 24) #x3DCCCCCC)))
(check-sat)
(exit)
