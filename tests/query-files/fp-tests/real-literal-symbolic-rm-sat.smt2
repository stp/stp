; RUN: %solver %s | %OutputCheck %s
;
; Control for the symbolic-rounding-mode tests: excluding only the value
; four of the five modes produce is satisfiable, by the mode that rounds
; the other way (RTP). If the ite collapsed to a single constant, or a
; branch were mislabeled, this would come out unsat.
(set-logic QF_FP)
(declare-const r RoundingMode)
(declare-const x (_ FloatingPoint 5 11))
(assert (= x ((_ to_fp 5 11) r 0.1)))
(assert (distinct x (fp #b0 #b01011 #b1001100110)))
; CHECK: ^sat
(check-sat)
