; RUN: %solver %s | %OutputCheck %s
;
; A fused multiply-add folded over literals whose product overflows the
; format. SymFPU's addition-result invariant bounded the exponent one short
; of what the product's exponent plus the carry reaches, and the folder's
; assertion aborted the solver; the sum is the overflow it says it is.
; CHECK: ^sat
(set-logic QF_FP)
(assert (= (fp.fma RNA (fp #b1 #b110 #b11111111) (fp #b1 #b110 #b11111111) (_ +zero 3 9)) (_ +oo 3 9)))
(check-sat)
