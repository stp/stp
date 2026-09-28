; RUN: %solver %s | %OutputCheck %s
;
; Directed rounding is outside the verified envelope, so the elimination
; must NOT fire; the query still solves through the ordinary circuit.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 11 53))
(assert (= x ((_ to_fp 8 24) #x3f800000)))
(assert (= ((_ to_fp 8 24) RTZ (fp.div RTZ ((_ to_fp 11 53) RNE x) u)) ((_ to_fp 8 24) #x40400000)))
(check-sat)
(exit)
