; RUN: %solver %s | %OutputCheck %s
;
; The constant folder takes the same SymFPU path as the symbolic encoding,
; so the (2, 4) collar wrap also folded (fp.roundToIntegral RNE 1.0) to a
; value other than 1.0 and answered unsat to a true equation.
; CHECK: ^sat
(set-logic QF_FP)
(assert (= (fp.roundToIntegral RNE (fp #b0 #b01 #b000)) (fp #b0 #b01 #b000)))
(check-sat)
