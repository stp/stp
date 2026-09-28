; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; SMT-LIB's to_fp-from-Real takes a rounding mode; without one the only
; one-argument form is the bit-reinterpreting to_fp of a bitvector. The
; diagnostic must say which piece is missing, not stop at a syntax error.
; CHECK: needs a rounding mode
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x ((_ to_fp 8 24) 1.5)))
(check-sat)
