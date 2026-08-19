; RUN: %solver %s | %OutputCheck %s
;
; The widened fp.lt against the float64 nearest 0.1 narrows to a float32
; comparison against the float32 just ABOVE it, so x >= that constant is
; unsatisfiable. The wrong rounding direction would answer sat.
;
; CHECK: ^unsat
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.lt ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) #x3FB999999999999A)))
(assert (fp.geq x ((_ to_fp 8 24) #x3DCCCCCD)))
(check-sat)
(exit)
