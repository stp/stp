; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)

; RoundingMode's five-bit carrier is not an unsigned BitVec operand.
; CHECK: to_fp_unsigned's argument must be a bitvector
(assert (fp.isNaN ((_ to_fp_unsigned 3 5) RNE RNE)))
(check-sat)
