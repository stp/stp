; RUN: %solver %s | %OutputCheck %s
;
; A real literal under a symbolic rounding mode becomes an ite over the
; value in all five modes (bitwuzla's shape). Pinning the mode by
; assertion must select exactly that mode's constant: 0.1 in Float16
; rounds up only under RTP, so with r forced to RTP the result cannot
; differ from the rounded-up constant.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 5 11))
(assert (= x ((_ to_fp 5 11) r 0.1)))
(assert (= r RTP))
(assert (distinct x (fp #b0 #b01011 #b1001100111)))
; CHECK: ^unsat
(check-sat)
