; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A rational constant is one ratio: division is not real arithmetic here,
; so (/ (/ 1 2) 3) is refused with the accepted spellings in the message.
; CHECK: does not nest
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x ((_ to_fp 8 24) RNE (/ (/ 1 2) 3))))
(check-sat)
