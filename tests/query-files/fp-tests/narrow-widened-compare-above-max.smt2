; RUN: %solver -d %s | %OutputCheck %s
;
; A wide constant just above float32's largest finite rounds down to that
; largest finite: only x = +oo exceeds it, and -d must produce it.
;
; CHECK: ^sat
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.gt ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) #x47EFFFFFE0000001)))
(check-sat)
(exit)
