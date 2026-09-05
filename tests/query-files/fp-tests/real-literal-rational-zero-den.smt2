; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; (/ 1 0) is not a rational constant -- there is no real it names -- so
; it is refused with a message saying which part is wrong. (For contrast,
; bitwuzla feeds it to GMP unchecked and dies on the division.)
; CHECK: must not be zero
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x ((_ to_fp 8 24) RNE (/ 1 0))))
(check-sat)
