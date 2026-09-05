; RUN: %solver %s | %OutputCheck %s
;
; A NaN numerator pins the narrowed quotient to NaN whatever the
; unconstrained divisor is: the elimination's stand-in keeps the
; classification, so asking for a non-NaN quotient stays unsatisfiable.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 11 53))
(assert (fp.isNaN x))
(assert (not (fp.isNaN ((_ to_fp 8 24) RNE (fp.div RNE ((_ to_fp 11 53) RNE x) u)))))
(check-sat)
(exit)
