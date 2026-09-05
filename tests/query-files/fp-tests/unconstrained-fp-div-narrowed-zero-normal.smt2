; RUN: %solver %s | %OutputCheck %s
;
; The other side of the zero-numerator class: no divisor makes 0/u a normal
; number, and the elimination's classification filter preserves that.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 11 53))
(assert (fp.isZero x))
(assert (= ((_ to_fp 8 24) RNE (fp.div RNE ((_ to_fp 11 53) RNE x) u)) ((_ to_fp 8 24) #x3f800000)))
(check-sat)
(exit)
