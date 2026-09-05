; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; LibBF encodes the exponent-field width in its flags, and its range
; starts at 3 bits. SMT-LIB additionally allows exponent width 2; a format
; that small cannot be folded, and the refusal says how to spell the value
; instead. (The sort itself is fine -- only the real-literal conversion is
; out of range.)
; CHECK: exponent widths from
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 2 8))
(assert (fp.eq x ((_ to_fp 2 8) RNE 1.5)))
(check-sat)
